// Package pointer provides a Go adaptation of [Steensgaard's pointer analysis algorithm].
//
// [Steensgaard's pointer analysis algorithm]: https://dl.acm.org/doi/abs/10.1145/237721.237727
package pointer

import (
	"errors"
	"fmt"
	"go/token"
	"go/types"
	"log"

	"github.com/BarrensZeppelin/pointer/internal/queue"
	"github.com/BarrensZeppelin/pointer/internal/slices"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/types/typeutil"
)

var ErrNotImplemented = errors.New("not implemented")

type aContext struct {
	config AnalysisConfig

	queue   queue.Queue[*ssa.Function]
	visited map[*ssa.Function]bool

	varToTerm map[ssa.Value]*term

	// Constraint var for the global panic argument
	panicVar *term

	// Shared type hasher
	tHasher typeutil.Hasher

	// Some memoized function pointers
	time_startTimer,
	godebug_setUpdate,
	sync_runtime_registerPoolCleanup *ssa.Function
}

func (ctx *aContext) eval(v ssa.Value) *term {
	switch v := v.(type) {
	case *ssa.Const:
		return mkFresh()

	case *ssa.Function:
		funs := map[*ssa.Function][]*term{v: nil}
		return t(tClosure{funs: funs, rval: mkFresh()})

	case *ssa.Alloc, *ssa.MakeChan, *ssa.MakeInterface,
		*ssa.MakeMap, *ssa.MakeSlice, *ssa.Global:
		return t(tPointsTo{
			x:     ctx.sterm(v),
			preps: []prePTag{prePSite{site: v}},
		})

	default:
		/*
			// Helpful to prevent bugs during development, but it's a bit expensive.
			switch v.(type) {
			case *ssa.Parameter, *ssa.FreeVar:
			default:
				if v.Name()[0] != 't' {
					log.Panicf("What??? %s %v", v.Name(), v)
				}
			} */

		/* if !PointerLike(v.Type()) {
			return mkFresh()
		} */

		return ctx.sterm(v)
	}
}

type AnalysisConfig struct {
	Program *ssa.Program

	// Functions in this list will be treated as program entry points.
	EntryFunctions []*ssa.Function
	// Packages in this list will have their main & init functions treated as
	// program entry points.
	EntryPackages []*ssa.Package

	// The following options are mainly useful for soundness comparison with
	// the analysis in "golang.org/x/tools/go/pointer". Setting them to true
	// makes the result an over-approximation of the result of that analysis.

	// When TreatMethodsAsRoots is true, all methods of all types in
	// prog.RuntimeTypes() are implicitly called.
	TreatMethodsAsRoots bool
	// Bind free variables when a closure is created instead of when it is
	// called. This makes the result less precise for bound methods that are
	// not called.
	BindFreeVarsEagerly bool
}

func Analyze(config AnalysisConfig) Result {
	prog := config.Program

	ctx := &aContext{
		config:    config,
		visited:   make(map[*ssa.Function]bool),
		varToTerm: make(map[ssa.Value]*term),
		panicVar:  mkFresh(),
		tHasher:   typeutil.MakeHasher(),
	}

	if godebug := prog.ImportedPackage("internal/godebug"); godebug != nil {
		ctx.godebug_setUpdate = godebug.Func("setUpdate")
	}
	if sync := prog.ImportedPackage("sync"); sync != nil {
		ctx.sync_runtime_registerPoolCleanup =
			sync.Func("sync.runtime_registerPoolCleanup")
	}
	if time := prog.ImportedPackage("time"); time != nil {
		ctx.time_startTimer = time.Func("startTimer")
	}
	if os := prog.ImportedPackage("os"); os != nil {
		// Allocate a synthetic slice for os.Args
		ctx.unify(
			ctx.sterm(os.Var("Args")),
			t(tPointsTo{
				x:     t(tArray{x: mkFresh()}),
				preps: []prePTag{prePSynth{label: "<command-line args>"}},
			}),
		)
	}

	var roots []*ssa.Function
	for _, pkg := range config.EntryPackages {
		for _, name := range [...]string{"main", "init"} {
			if fun := pkg.Func(name); fun != nil {
				ctx.discoverFun(fun)
				roots = append(roots, fun)
			}
		}
	}

	for _, fun := range config.EntryFunctions {
		ctx.discoverFun(fun)
		roots = append(roots, fun)
	}

	if config.TreatMethodsAsRoots {
		for _, T := range prog.RuntimeTypes() {
			mset := prog.MethodSets.MethodSet(T)
			for i, n := 0, mset.Len(); i < n; i++ {
				m := prog.MethodValue(mset.At(i))
				ctx.discoverFun(m)
			}
		}
	}

	// Main analysis loop
	for !ctx.queue.Empty() {
		// Process functions from the queue until it is empty
		for !ctx.queue.Empty() {
			ctx.processFunc(ctx.queue.Pop())
		}

		// Process calls to runtime.SetFinalizer. The outer loop will break if
		// we don't see any new functions to process.
		if runtime := prog.ImportedPackage("runtime"); runtime != nil {
			fun := runtime.Func("SetFinalizer")

			objIT := t(ctx.zeroTermForType(fun.Params[0].Type()))
			objT := ctx.eval(fun.Params[0])
			ctx.unify(objT, t(tPointsTo{x: objIT}))
			obj := find(objIT).x.(tInterface)

			if obj.contents.Len() == 0 {
				break
			}

			funsT := t(ctx.zeroTermForType(fun.Params[1].Type()))
			ctx.unify(ctx.eval(fun.Params[1]), t(tPointsTo{x: funsT}))
			funs := find(funsT).x.(tInterface)

			if funs.contents.Len() == 0 {
				break
			}

			funs.contents.Iterate(func(fType types.Type, fTerm *term) {
				fSig, ok := fType.Underlying().(*types.Signature)
				if !ok || fSig.Recv() != nil || fSig.Params().Len() != 1 {
					return
				}

				pType := fSig.Params().At(0).Type()
				if types.IsInterface(pType) {
					ctx.unify(fTerm,
						t(tClosure{
							called: true,
							funs:   make(map[*ssa.Function][]*term),
							args:   []*term{objT},
							rval:   mkFresh(),
						}))
				} else {
					obj.contents.Iterate(func(oType types.Type, v *term) {
						if !types.AssignableTo(oType, pType) {
							return
						}

						ctx.unify(fTerm,
							t(tClosure{
								called: true,
								funs:   make(map[*ssa.Function][]*term),
								args:   []*term{v},
								rval:   mkFresh(),
							}))
					})
				}
			})
		}
	}

	r := prog.NewFunction("<root>", new(types.Signature), "root of callgraph")
	cg := callgraph.New(r)

	// Add call edges for root function
	for _, fun := range roots {
		callgraph.AddEdge(cg.CreateNode(r), nil, cg.CreateNode(fun))
	}

	result := ctx.result(cg)

	/* for fun := range ctx.visited {
		fmt.Println("Result for", fun)
		for bi, b := range fun.Blocks {
			fmt.Printf("-- block %d\n", bi)
			for _, i := range b.Instrs {
				switch v := i.(type) {
				case ssa.Value:
					ptr := "Ø"
					if term := ctx.varToTerm[v]; term != nil {
						term = find(term)
						// ptr = fmt.Sprintf("%q %v", ptsto(term), find(term))
						switch t := term.x.(type) {
						case PointsTo, Closure:
							ptr = fmt.Sprintf("%v", result.resolve(term))
						default:
							ptr = fmt.Sprintf("%T %v", t, t)
						}
					}

					fmt.Printf("%s = %s\t\t%v\n", v.Name(), v, ptr)
				default:
					fmt.Println(v)
				}
			}
		}
	} */

	return result
}

func (ctx *aContext) processFunc(fun *ssa.Function) {
	// Helper function for constructing a points-to term with a singleton set
	// for the sites field.
	alloc := func(site ssa.Value, content *term) *term {
		return t(tPointsTo{
			x:     content,
			preps: []prePTag{prePSite{site: site}},
		})
	}

	handleBuiltin := func(call ssa.CallInstruction) {
		common := call.Common()
		rval := mkFresh()
		if v := call.Value(); v != nil {
			rval = ctx.sterm(v)
		}

		switch common.Value.Name() {
		case "append":
			el := t(tArray{x: mkFresh()})
			ctx.unify(rval, alloc(call.Value(), el))
			ctx.unify(rval, ctx.eval(common.Args[0]))
			ctx.unify(ctx.eval(common.Args[1]), t(tPointsTo{x: el}))
		case "recover":
			ctx.unify(ctx.panicVar, ctx.eval(call.Value()))
		case "ssa:wrapnilchk":
			arg := ctx.eval(common.Args[0])
			ctx.unify(arg, t(tPointsTo{x: mkFresh()}))
			ctx.unify(arg, rval)
		case "copy":
			el := t(tArray{x: mkFresh()})
			ctx.unify(ctx.eval(common.Args[0]), t(tPointsTo{x: el}))
			ctx.unify(ctx.eval(common.Args[1]), t(tPointsTo{x: el}))
		}
	}

	modelFun := func(call ssa.CallInstruction) bool {
		common := call.Common()
		sc := common.StaticCallee()
		if sc == nil {
			return false
		}

		switch {
		case sc == ctx.godebug_setUpdate,
			sc == ctx.sync_runtime_registerPoolCleanup:
			// Immediately treat argument as called
			f := common.Args[0]
			args := make([]*term, f.Type().(*types.Signature).Params().Len())
			for i := range args {
				args[i] = mkFresh()
			}

			ctx.unify(ctx.eval(common.Args[0]),
				t(tClosure{
					funs:   make(map[*ssa.Function][]*term),
					called: true,
					args:   args,
					rval:   mkFresh(),
				}))
			return true

		case sc == ctx.time_startTimer:
			argT := sc.Signature.Params().At(0).Type()
			runtimeTimerT := argT.(*types.Pointer).Elem().Underlying().(*types.Struct)

			fI := FieldIndex(runtimeTimerT, "f")
			argI := FieldIndex(runtimeTimerT, "arg")

			// Model startTimer as calling the function in the field 'f' of the
			// provided runtimeTimer with the argument in field 'arg'.
			fStruct := ctx.zeroTermForType(runtimeTimerT).(tStruct)
			fStruct.fields[argI] = mkFresh()
			fStruct.fields[fI] = t(tClosure{
				called: true,
				funs:   make(map[*ssa.Function][]*term),
				args:   []*term{fStruct.fields[argI], mkFresh()},
				rval:   mkFresh(),
			})

			ctx.unify(ctx.eval(common.Args[0]), t(tPointsTo{x: t(fStruct)}))

			return true

		default:
			return false
		}
	}

	for _, block := range fun.Blocks {
		for _, insn := range block.Instrs {
			switch insn := insn.(type) {
			case ssa.CallInstruction:
				common := insn.Common()

				rval := mkFresh()
				if v := insn.Value(); v != nil {
					rval = ctx.sterm(v)
				}

				if common.IsInvoke() {
					recv := common.Value
					itf := ctx.zeroTermForType(recv.Type()).(tInterface)
					itf.calledMethods[common.Method] = method{
						slices.Map(common.Args, ctx.eval),
						rval,
					}

					ctx.unify(ctx.eval(recv), t(tPointsTo{x: t(itf)}))
				} else if _, ok := common.Value.(*ssa.Builtin); ok {
					handleBuiltin(insn)
				} else if !modelFun(insn) {
					closure := tClosure{
						funs:   make(map[*ssa.Function][]*term),
						called: true,
						args:   slices.Map(common.Args, ctx.eval),
						rval:   rval,
					}

					ctx.unify(ctx.eval(common.Value), t(closure))
				}

			case ssa.Value:
				/* if !PointerLike(insn.Type()) {
					continue
				} */

				reg := ctx.sterm(insn)
				switch insn := insn.(type) {
				case *ssa.Alloc:
					// handled in eval

				case *ssa.MakeChan:
					ctx.unify(reg, t(tChan{payload: mkFresh()}))

				case *ssa.MakeClosure:
					fun := insn.Fn.(*ssa.Function)
					fvs := slices.Map(insn.Bindings, ctx.eval)
					funs := map[*ssa.Function][]*term{fun: fvs}

					if ctx.config.BindFreeVarsEagerly {
						for i, fv := range fun.FreeVars {
							ctx.unify(ctx.sterm(fv), fvs[i])
						}
					}

					ctx.unify(reg, t(tClosure{funs: funs, rval: mkFresh()}))

				case *ssa.MakeSlice:
					ctx.unify(reg, t(tArray{x: mkFresh()}))

				case *ssa.MakeInterface:
					itf := ctx.zeroTermForType(insn.Type()).(tInterface)
					itf.contents.Set(insn.X.Type(), ctx.eval(insn.X))

					ctx.unify(reg, t(itf))

				case *ssa.MakeMap:
					ctx.unify(reg, t(tMap{keys: mkFresh(), values: mkFresh()}))

				case *ssa.UnOp:
					rhs := ctx.eval(insn.X)
					switch insn.Op {
					case token.MUL:
						ctx.unify(rhs, t(tPointsTo{x: reg}))

					case token.ARROW:
						res := mkFresh()
						ctx.unify(rhs, t(tPointsTo{x: t(tChan{payload: res})}))

						if insn.CommaOk {
							fStruct := ctx.zeroTermForType(insn.Type()).(tStruct)
							fStruct.fields[0] = res
							res = t(fStruct)
						}

						ctx.unify(reg, res)
					}

				case *ssa.Convert:
					switch insn.Type().Underlying().(type) {
					case *types.Pointer:
						if bt, ok := insn.X.Type().Underlying().(*types.Basic); !ok ||
							bt.Kind() != types.UnsafePointer {
							log.Panicf("??? %v", insn.X)
						}

						// Treat conversion from unsafe pointer to pointer as a new allocation
						ctx.unify(reg, alloc(insn, mkFresh()))

					case *types.Slice:
						ctx.unify(reg, alloc(insn, t(tArray{x: mkFresh()})))
					}

				case *ssa.ChangeType:
					ctx.unify(reg, ctx.eval(insn.X))

				case *ssa.ChangeInterface:
					ctx.unify(reg, ctx.eval(insn.X))

				case *ssa.Slice:
					ctx.unify(reg, ctx.eval(insn.X))

				case *ssa.SliceToArrayPointer:
					ctx.unify(reg, ctx.eval(insn.X))

				case *ssa.IndexAddr:
					fresh := mkFresh()
					base := ctx.eval(insn.X)
					ctx.unify(base, t(tPointsTo{x: t(tArray{x: fresh})}))
					ctx.unify(reg, t(tPointsTo{
						x:     fresh,
						preps: []prePTag{prePAccess{base: base, field: -1}},
					}))

				case *ssa.Index:
					switch insn.X.Type().Underlying().(type) {
					case *types.Array:
						ctx.unify(ctx.eval(insn.X), t(tArray{x: reg}))
					case *types.Basic:
					default:
						log.Panicf("Unhandled index on %T", insn.X.Type())
					}

				case *ssa.FieldAddr:
					sTyp := insn.X.Type().Underlying().(*types.Pointer).Elem()
					fStruct := ctx.zeroTermForType(sTyp).(tStruct)
					fresh := mkFresh()
					fStruct.fields[insn.Field] = fresh

					base := ctx.eval(insn.X)
					ctx.unify(base, t(tPointsTo{x: t(fStruct)}))
					ctx.unify(reg, t(tPointsTo{
						x:     fresh,
						preps: []prePTag{prePAccess{base: base, field: insn.Field}},
					}))

				case *ssa.Field:
					fStruct := ctx.zeroTermForType(insn.X.Type()).(tStruct)
					fStruct.fields[insn.Field] = reg
					ctx.unify(ctx.eval(insn.X), t(fStruct))

				case *ssa.Lookup:
					res := mkFresh()
					ctx.unify(ctx.eval(insn.X),
						t(tPointsTo{x: t(tMap{keys: mkFresh(), values: res})}))

					if insn.CommaOk {
						fStruct := ctx.zeroTermForType(insn.Type()).(tStruct)
						fStruct.fields[0] = res
						res = t(fStruct)
					}

					ctx.unify(reg, res)

				case *ssa.Phi:
					for _, v := range insn.Edges {
						ctx.unify(reg, ctx.eval(v))
					}

				case *ssa.Select:
					fields := []*term{mkFresh(), mkFresh()}
					for _, v := range insn.States {
						if v.Dir == types.RecvOnly {
							fresh := mkFresh()
							ctx.unify(ctx.eval(v.Chan),
								t(tPointsTo{x: t(tChan{payload: fresh})}))
							fields = append(fields, fresh)
						} else {
							ctx.unify(ctx.eval(v.Chan),
								t(tPointsTo{x: t(tChan{payload: ctx.eval(v.Send)})}))
						}
					}

					ctx.unify(reg, t(tStruct{fields: fields}))

				case *ssa.Extract:
					fStruct := ctx.zeroTermForType(insn.Tuple.Type()).(tStruct)
					fStruct.fields[insn.Index] = reg

					ctx.unify(ctx.eval(insn.Tuple), t(fStruct))

				case *ssa.TypeAssert:
					res := mkFresh()

					if _, isItf := insn.AssertedType.Underlying().(*types.Interface); isItf {
						ctx.unify(res, ctx.eval(insn.X))
					} else {
						fItf := ctx.zeroTermForType(insn.X.Type()).(tInterface)
						fItf.contents.Set(insn.AssertedType, res)
						ctx.unify(ctx.eval(insn.X), t(tPointsTo{x: t(fItf)}))
					}

					if insn.CommaOk {
						fStruct := ctx.zeroTermForType(insn.Type()).(tStruct)
						fStruct.fields[0] = res
						res = t(fStruct)
					}

					ctx.unify(reg, res)

				case *ssa.Range:
					if _, isMap := insn.X.Type().Underlying().(*types.Map); isMap {
						ctx.unify(reg, ctx.eval(insn.X))
					}
					// Disregard string ranges

				case *ssa.Next:
					if !insn.IsString {
						k, v := mkFresh(), mkFresh()
						ctx.unify(ctx.eval(insn.Iter),
							t(tPointsTo{x: t(tMap{keys: k, values: v})}))

						fStruct := ctx.zeroTermForType(insn.Type()).(tStruct)
						fStruct.fields[1] = k
						fStruct.fields[2] = v
						ctx.unify(reg, t(fStruct))
					}
					// Disregard string ranges

				case *ssa.BinOp:

				default:
					log.Panicf("Unhandled: %T %v", insn, insn)
				}

			case *ssa.Store:
				lhs := ctx.eval(insn.Addr)
				rhs := ctx.eval(insn.Val)
				ctx.unify(lhs, t(tPointsTo{x: rhs}))

			case *ssa.Send:
				lhs := ctx.eval(insn.Chan)
				rhs := ctx.eval(insn.X)
				ctx.unify(lhs, t(tPointsTo{x: t(tChan{payload: rhs})}))

			case *ssa.MapUpdate:
				ctx.unify(ctx.eval(insn.Map),
					t(tPointsTo{x: t(tMap{
						keys:   ctx.eval(insn.Key),
						values: ctx.eval(insn.Value),
					})}))

			case *ssa.Panic:
				ctx.unify(ctx.panicVar, ctx.eval(insn.X))

			case *ssa.Return,
				*ssa.RunDefers,
				*ssa.If,
				*ssa.Jump:

			default:
				log.Panicf("Unhandled: %T %v", insn, insn)
			}
		}
	}
}

func PrintSSAFun(fun *ssa.Function) {
	fmt.Println(fun.Name())
	for bi, b := range fun.Blocks {
		fmt.Println(bi, ":")
		for _, i := range b.Instrs {
			switch v := i.(type) {
			case *ssa.DebugRef:
				// skip
			case ssa.Value:
				fmt.Println(v.Name(), "=", v)
			default:
				fmt.Println(i)
			}
		}
	}
}
