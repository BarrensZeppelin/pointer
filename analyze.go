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

	varToTerm map[ssa.Value]*Term

	// Constraint var for the global panic argument
	panicVar *Term

	// Shared type hasher
	tHasher typeutil.Hasher

	// Some memoized function pointers
	time_startTimer,
	godebug_setUpdate,
	sync_runtime_registerPoolCleanup *ssa.Function
}

func (ctx *aContext) eval(v ssa.Value) *Term {
	switch v := v.(type) {
	case *ssa.Const:
		return mkFresh()

	case *ssa.Function:
		funs := map[*ssa.Function][]*Term{v: nil}
		return T(Closure{funs: funs, rval: mkFresh()})

	case *ssa.Alloc, *ssa.MakeChan, *ssa.MakeInterface,
		*ssa.MakeMap, *ssa.MakeSlice, *ssa.Global:
		return T(PointsTo{
			x: ctx.sterm(v),
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
		varToTerm: make(map[ssa.Value]*Term),
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

			objIT := T(ctx.zeroTermForType(fun.Params[0].Type()))
			objT := ctx.eval(fun.Params[0])
			ctx.unify(objT, T(PointsTo{x: objIT}))
			obj := find(objIT).x.(Interface)

			if obj.contents.Len() == 0 {
				break
			}

			funsT := T(ctx.zeroTermForType(fun.Params[1].Type()))
			ctx.unify(ctx.eval(fun.Params[1]), T(PointsTo{x: funsT}))
			funs := find(funsT).x.(Interface)

			if funs.contents.Len() == 0 {
				break
			}

			funs.contents.Iterate(func(fType types.Type, v any) {
				fTerm := v.(*Term)
				fSig, ok := fType.Underlying().(*types.Signature)
				if !ok || fSig.Recv() != nil || fSig.Params().Len() != 1 {
					return
				}

				pType := fSig.Params().At(0).Type()
				if types.IsInterface(pType) {
					ctx.unify(fTerm,
						T(Closure{
							called: true,
							funs:   make(map[*ssa.Function][]*Term),
							args:   []*Term{objT},
							rval:   mkFresh(),
						}))
				} else {
					obj.contents.Iterate(func(oType types.Type, v any) {
						if !types.AssignableTo(oType, pType) {
							return
						}

						ctx.unify(fTerm,
							T(Closure{
								called: true,
								funs:   make(map[*ssa.Function][]*Term),
								args:   []*Term{v.(*Term)},
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

	for fun := range ctx.visited {
		n := cg.CreateNode(fun)

		for _, block := range fun.Blocks {
			for _, insn := range block.Instrs {
				call, ok := insn.(ssa.CallInstruction)
				if !ok {
					continue
				}

				common := call.Common()
				v := common.Value

				var callees []*ssa.Function
				if common.IsInvoke() {
					if pt, ok := find(ctx.eval(v)).x.(PointsTo); ok {
						find(pt.x).x.(Interface).iterateCallees(
							ctx.config.Program,
							common.Method,
							func(fun *ssa.Function, _ *Term) {
								callees = append(callees, fun)
							})
					}
				} else if _, isBuiltin := v.(*ssa.Builtin); !isBuiltin {
					if sc := common.StaticCallee(); sc != nil &&
						sc == ctx.time_startTimer {

						argT := sc.Signature.Params().At(0).Type().(*types.Pointer)
						runtimeTimerT := argT.Elem().Underlying().(*types.Struct)

						fI := FieldIndex(runtimeTimerT, "f")
						arg := find(ctx.eval(common.Args[0]))
						strukt := find(arg.x.(PointsTo).x).x.(Struct)
						closure := find(strukt.fields[fI]).x.(Closure)

						for fun := range closure.funs {
							callgraph.AddEdge(cg.CreateNode(sc), nil, cg.CreateNode(fun))
						}
					}

					closure, _ := find(ctx.eval(v)).x.(Closure)
					for fun := range closure.funs {
						callees = append(callees, fun)
					}
				}

				for _, callee := range callees {
					callgraph.AddEdge(n, call, cg.CreateNode(callee))
				}
			}
		}
	}

	// Add call edges for runtime.SetFinalizer calls
	if runtime := prog.ImportedPackage("runtime"); runtime != nil {
		fun := runtime.Func("SetFinalizer")

		var callers []ssa.CallInstruction
		for _, ed := range cg.CreateNode(fun).In {
			callers = append(callers, ed.Site)
		}

		if len(callers) == 0 {
			goto DONE
		}

		obj := find(find(ctx.eval(fun.Params[0])).x.(PointsTo).x).x.(Interface)
		if obj.contents.Len() == 0 {
			goto DONE
		}

		funs := find(find(ctx.eval(fun.Params[1])).x.(PointsTo).x).x.(Interface)
		if funs.contents.Len() == 0 {
			goto DONE
		}

		funs.contents.Iterate(func(fType types.Type, v any) {
			fSig, ok := fType.Underlying().(*types.Signature)
			if !ok || fSig.Recv() != nil || fSig.Params().Len() != 1 {
				return
			}

			clos, ok := find(v.(*Term)).x.(Closure)
			if !ok {
				return
			}

			pType := fSig.Params().At(0).Type()
			anyWorks := false
			obj.contents.Iterate(func(oType types.Type, _ any) {
				anyWorks = anyWorks || types.AssignableTo(oType, pType)
			})

			if anyWorks {
				for fun := range clos.funs {
					for _, caller := range callers {
						callgraph.AddEdge(
							cg.CreateNode(caller.Parent()),
							caller,
							cg.CreateNode(fun))
					}
				}
			}
		})
	}
DONE:

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
	alloc := func(site ssa.Value, content *Term) *Term {
		return T(PointsTo{
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
			el := T(Array{x: mkFresh()})
			ctx.unify(rval, alloc(call.Value(), el))
			ctx.unify(rval, ctx.eval(common.Args[0]))
			ctx.unify(ctx.eval(common.Args[1]), T(PointsTo{x: el}))
		case "recover":
			ctx.unify(ctx.panicVar, ctx.eval(call.Value()))
		case "ssa:wrapnilchk":
			arg := ctx.eval(common.Args[0])
			ctx.unify(arg, T(PointsTo{x: mkFresh()}))
			ctx.unify(arg, rval)
		case "copy":
			el := T(Array{x: mkFresh()})
			ctx.unify(ctx.eval(common.Args[0]), T(PointsTo{x: el}))
			ctx.unify(ctx.eval(common.Args[1]), T(PointsTo{x: el}))
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
			args := make([]*Term, f.Type().(*types.Signature).Params().Len())
			for i := range args {
				args[i] = mkFresh()
			}

			ctx.unify(ctx.eval(common.Args[0]),
				T(Closure{
					funs:   make(map[*ssa.Function][]*Term),
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
			fStruct := ctx.zeroTermForType(runtimeTimerT).(Struct)
			fStruct.fields[argI] = mkFresh()
			fStruct.fields[fI] = T(Closure{
				called: true,
				funs:   make(map[*ssa.Function][]*Term),
				args:   []*Term{fStruct.fields[argI], mkFresh()},
				rval:   mkFresh(),
			})

			ctx.unify(ctx.eval(common.Args[0]), T(PointsTo{x: T(fStruct)}))

			return true

		default:
			return false
		}
	}

	for _, block := range fun.Blocks {
		for _, insn := range block.Instrs {
			switch t := insn.(type) {
			case ssa.CallInstruction:
				common := t.Common()

				rval := mkFresh()
				if v := t.Value(); v != nil {
					rval = ctx.sterm(v)
				}

				if common.IsInvoke() {
					recv := common.Value
					itf := ctx.zeroTermForType(recv.Type()).(Interface)
					itf.calledMethods[common.Method] = method{
						slices.Map(common.Args, ctx.eval),
						rval,
					}

					ctx.unify(ctx.eval(recv), T(PointsTo{x: T(itf)}))
				} else if _, ok := common.Value.(*ssa.Builtin); ok {
					handleBuiltin(t)
				} else if !modelFun(t) {
					closure := Closure{
						funs:   make(map[*ssa.Function][]*Term),
						called: true,
						args:   slices.Map(common.Args, ctx.eval),
						rval:   rval,
					}

					ctx.unify(ctx.eval(common.Value), T(closure))
				}

			case ssa.Value:
				/* if !PointerLike(t.Type()) {
					continue
				} */

				reg := ctx.sterm(t)
				switch t := t.(type) {
				case *ssa.Alloc:
					// handled in eval

				case *ssa.MakeChan:
					ctx.unify(reg, T(Chan{payload: mkFresh()}))

				case *ssa.MakeClosure:
					fun := t.Fn.(*ssa.Function)
					fvs := slices.Map(t.Bindings, ctx.eval)
					funs := map[*ssa.Function][]*Term{fun: fvs}

					if ctx.config.BindFreeVarsEagerly {
						for i, fv := range fun.FreeVars {
							ctx.unify(ctx.sterm(fv), fvs[i])
						}
					}

					ctx.unify(reg, T(Closure{funs: funs, rval: mkFresh()}))

				case *ssa.MakeSlice:
					ctx.unify(reg, T(Array{x: mkFresh()}))

				case *ssa.MakeInterface:
					itf := ctx.zeroTermForType(t.Type()).(Interface)
					itf.contents.Set(t.X.Type(), ctx.eval(t.X))

					ctx.unify(reg, T(itf))

				case *ssa.MakeMap:
					ctx.unify(reg, T(Map{keys: mkFresh(), values: mkFresh()}))

				case *ssa.UnOp:
					rhs := ctx.eval(t.X)
					switch t.Op {
					case token.MUL:
						ctx.unify(rhs, T(PointsTo{x: reg}))

					case token.ARROW:
						res := mkFresh()
						ctx.unify(rhs, T(PointsTo{x: T(Chan{payload: res})}))

						if t.CommaOk {
							fStruct := ctx.zeroTermForType(t.Type()).(Struct)
							fStruct.fields[0] = res
							res = T(fStruct)
						}

						ctx.unify(reg, res)
					}

				case *ssa.Convert:
					switch t.Type().Underlying().(type) {
					case *types.Pointer:
						if bt, ok := t.X.Type().Underlying().(*types.Basic); !ok ||
							bt.Kind() != types.UnsafePointer {
							log.Panicf("??? %v", t.X)
						}

						// Treat conversion from unsafe pointer to pointer as a new allocation
						ctx.unify(reg, alloc(t, mkFresh()))

					case *types.Slice:
						ctx.unify(reg, alloc(t, T(Array{x: mkFresh()})))
					}

				case *ssa.ChangeType:
					ctx.unify(reg, ctx.eval(t.X))

				case *ssa.ChangeInterface:
					ctx.unify(reg, ctx.eval(t.X))

				case *ssa.Slice:
					ctx.unify(reg, ctx.eval(t.X))

				case *ssa.SliceToArrayPointer:
					ctx.unify(reg, ctx.eval(t.X))

				case *ssa.IndexAddr:
					fresh := mkFresh()
					base := ctx.eval(t.X)
					ctx.unify(base, T(PointsTo{x: T(Array{x: fresh})}))
					ctx.unify(reg, T(PointsTo{
						x:     fresh,
						preps: []prePTag{prePAccess{base: base, field: -1}},
					}))

				case *ssa.Index:
					switch t.X.Type().Underlying().(type) {
					case *types.Array:
						ctx.unify(ctx.eval(t.X), T(Array{x: reg}))
					case *types.Basic:
					default:
						log.Panicf("Unhandled index on %T", t.X.Type())
					}

				case *ssa.FieldAddr:
					sTyp := t.X.Type().Underlying().(*types.Pointer).Elem()
					fStruct := ctx.zeroTermForType(sTyp).(Struct)
					fresh := mkFresh()
					fStruct.fields[t.Field] = fresh

					base := ctx.eval(t.X)
					ctx.unify(base, T(PointsTo{x: T(fStruct)}))
					ctx.unify(reg, T(PointsTo{
						x:     fresh,
						preps: []prePTag{prePAccess{base: base, field: t.Field}},
					}))

				case *ssa.Field:
					fStruct := ctx.zeroTermForType(t.X.Type()).(Struct)
					fStruct.fields[t.Field] = reg
					ctx.unify(ctx.eval(t.X), T(fStruct))

				case *ssa.Lookup:
					res := mkFresh()
					ctx.unify(ctx.eval(t.X),
						T(PointsTo{x: T(Map{keys: mkFresh(), values: res})}))

					if t.CommaOk {
						fStruct := ctx.zeroTermForType(t.Type()).(Struct)
						fStruct.fields[0] = res
						res = T(fStruct)
					}

					ctx.unify(reg, res)

				case *ssa.Phi:
					for _, v := range t.Edges {
						ctx.unify(reg, ctx.eval(v))
					}

				case *ssa.Select:
					fields := []*Term{mkFresh(), mkFresh()}
					for _, v := range t.States {
						if v.Dir == types.RecvOnly {
							fresh := mkFresh()
							ctx.unify(ctx.eval(v.Chan),
								T(PointsTo{x: T(Chan{payload: fresh})}))
							fields = append(fields, fresh)
						} else {
							ctx.unify(ctx.eval(v.Chan),
								T(PointsTo{x: T(Chan{payload: ctx.eval(v.Send)})}))
						}
					}

					ctx.unify(reg, T(Struct{fields: fields}))

				case *ssa.Extract:
					fStruct := ctx.zeroTermForType(t.Tuple.Type()).(Struct)
					fStruct.fields[t.Index] = reg

					ctx.unify(ctx.eval(t.Tuple), T(fStruct))

				case *ssa.TypeAssert:
					res := mkFresh()

					if _, isItf := t.AssertedType.Underlying().(*types.Interface); isItf {
						ctx.unify(res, ctx.eval(t.X))
					} else {
						fItf := ctx.zeroTermForType(t.X.Type()).(Interface)
						fItf.contents.Set(t.AssertedType, res)
						ctx.unify(ctx.eval(t.X), T(PointsTo{x: T(fItf)}))
					}

					if t.CommaOk {
						fStruct := ctx.zeroTermForType(t.Type()).(Struct)
						fStruct.fields[0] = res
						res = T(fStruct)
					}

					ctx.unify(reg, res)

				case *ssa.Range:
					if _, isMap := t.X.Type().Underlying().(*types.Map); isMap {
						ctx.unify(reg, ctx.eval(t.X))
					}
					// Disregard string ranges

				case *ssa.Next:
					if !t.IsString {
						k, v := mkFresh(), mkFresh()
						ctx.unify(ctx.eval(t.Iter),
							T(PointsTo{x: T(Map{keys: k, values: v})}))

						fStruct := ctx.zeroTermForType(t.Type()).(Struct)
						fStruct.fields[1] = k
						fStruct.fields[2] = v
						ctx.unify(reg, T(fStruct))
					}
					// Disregard string ranges

				case *ssa.BinOp:

				default:
					log.Panicf("Unhandled: %T %v", t, t)
				}

			case *ssa.Store:
				lhs := ctx.eval(t.Addr)
				rhs := ctx.eval(t.Val)
				ctx.unify(lhs, T(PointsTo{x: rhs}))

			case *ssa.Send:
				lhs := ctx.eval(t.Chan)
				rhs := ctx.eval(t.X)
				ctx.unify(lhs, T(PointsTo{x: T(Chan{payload: rhs})}))

			case *ssa.MapUpdate:
				ctx.unify(ctx.eval(t.Map),
					T(PointsTo{x: T(Map{
						keys:   ctx.eval(t.Key),
						values: ctx.eval(t.Value),
					})}))

			case *ssa.Panic:
				ctx.unify(ctx.panicVar, ctx.eval(t.X))

			case *ssa.Return,
				*ssa.RunDefers,
				*ssa.If,
				*ssa.Jump:

			default:
				log.Panicf("Unhandled: %T %v", t, t)
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
