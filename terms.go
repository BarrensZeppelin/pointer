package pointer

import (
	"fmt"
	"go/types"
	"log"

	"github.com/BarrensZeppelin/pointer/internal/slices"
	"golang.org/x/tools/go/ssa"
)

type termTag interface {
	// method used to tag term constructors
	termTag()
	fmt.Stringer
}

type ttag struct{}

func (ttag) termTag() {}

type tFresh struct {
	ttag
	index int
}

func (f tFresh) String() string {
	return fmt.Sprintf("α%d", f.index)
}

/* type tSite struct {
	ttag
	ssa.Value
	Register bool
}

func (s tSite) String() string {
	if s.Register {
		return s.Name()
	}
	return fmt.Sprintf("%s = %v", s.Name(), s.Value.String())
} */

type tPointsTo struct {
	ttag
	// The term representing the pointed to objects
	x *term
	// List of points-to "pre-" constraints collected during solving.
	// These are used afterwards to reconstruct the points-to relation.
	preps []prePTag
}

func (c tPointsTo) String() string {
	return fmt.Sprintf("↑ %T", find(c.x).x)
}

type tChan struct {
	ttag
	payload *term
}

func (c tChan) String() string {
	return fmt.Sprintf("Chan(%v)", find(c.payload))
}

type tArray struct {
	ttag
	x *term
}

func (a tArray) String() string {
	return fmt.Sprintf("Array(%v)", find(a.x))
}

type tMap struct {
	ttag
	keys   *term
	values *term
}

func (m tMap) String() string {
	return fmt.Sprintf("Map(%v ↦ %v)", find(m.keys), find(m.values))
}

type tStruct struct {
	ttag
	fields []*term
}

func (s tStruct) String() string {
	var inner []string
	for i, field := range s.fields {
		inner = append(inner, fmt.Sprintf("%d ↦ %v", i, find(field)))
	}
	return fmt.Sprintf("Struct(%v)", inner)
}

type tClosure struct {
	ttag
	called bool
	funs   map[*ssa.Function][]*term
	args   []*term
	rval   *term
}

func (c tClosure) String() string {
	var inner []string
	for fun, fvs := range c.funs {
		inner = append(inner, fmt.Sprintf("%v ↦ %v", fun, slices.Map(fvs, find)))
	}
	return fmt.Sprintf("Closure(%v)", inner)
}

type method struct {
	args []*term
	rval *term
}

type tInterface struct {
	ttag
	contents      *typemap[*term]
	calledMethods map[*types.Func]method
}

func (i tInterface) String() string {
	var inner []string
	i.contents.Iterate(func(t types.Type, v *term) {
		inner = append(inner, fmt.Sprintf("%v ↦ %v", t, find(v)))
	})
	return fmt.Sprintf("Interface(%v)", inner)
}

func (i tInterface) iterateCallees(
	prog *ssa.Program,
	method *types.Func,
	f func(fun *ssa.Function, recv *term),
) {
	recv := method.Type().(*types.Signature).Recv().Type().Underlying().(*types.Interface)
	i.contents.Iterate(func(key types.Type, v *term) {
		ms := prog.MethodSets.MethodSet(key)
		if sel := ms.Lookup(method.Pkg(), method.Name()); sel != nil &&
			// Check that the selected method (selected on name only) has the
			// correct type.
			types.Identical(sel.Type(), method.Type()) {

			// Make sure that the receiver actually implements the expected interface.
			if !types.Implements(key, recv) {
				return
			}

			fun := prog.MethodValue(sel)
			f(fun, v)
		}
	})
}

type term struct {
	x      termTag
	parent *term
}

func (t *term) String() string {
	return fmt.Sprint(t.x)
}

func t(x termTag) *term {
	return &term{x: x}
}

func find(t *term) *term {
	if t.parent == nil {
		return t
	}
	t.parent = find(t.parent)
	return t.parent
}

// union makes `b` the parent of `a`.
func union(a, b *term) {
	if a.parent != nil || b.parent != nil {
		panic("union arguments should be representatives")
	}

	a.parent = b
}

func unificationError(a, b termTag) error {
	return fmt.Errorf("unable to unify terms of type %T and %T", a, b)
}

func (ctx *aContext) discoverFun(fun *ssa.Function) {
	if !ctx.visited[fun] {
		if fun.TypeParams().Len() > len(fun.TypeArgs()) {
			log.Fatalf(`%s: discovered uninstantiated call to generic function %s
(build with ssa.InstantiateGenerics)`,
				ctx.config.Program.Fset.Position(fun.Pos()), fun.String())
		}

		ctx.visited[fun] = true
		ctx.queue.Push(fun)
	}
}

func (ctx *aContext) call(fun *ssa.Function, args []*term, fvs []*term, rval *term) {
	ctx.discoverFun(fun)

	for i, fv := range fun.FreeVars {
		ctx.unify(ctx.sterm(fv), fvs[i])
	}

	for i, a := range fun.Params {
		ctx.unify(ctx.sterm(a), args[i])
	}

	for _, block := range fun.Blocks {
		if ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return); ok {
			switch len(ret.Results) {
			case 0:
			case 1:
				ctx.unify(rval, ctx.eval(ret.Results[0]))
			default:
				ctx.unify(rval, t(tStruct{fields: slices.Map(ret.Results, ctx.eval)}))
			}
		}
	}
}

func checkLen[L ~[]T, T any](a, b L, msg string) {
	if len(a) != len(b) {
		log.Panicf("%s: %v (%d) != %v (%d)", msg, a, len(a), b, len(b))
	}
}

func (ctx *aContext) unify(a, b *term) {
	a, b = find(a), find(b)
	if a == b {
		return
	}

	// Implementation here is a bit finnicky.
	// It seems it like it should be simple enough, but due to reentrancy we
	// have to make sure that the immediate effects of the current unify are
	// applied before calling unify recursively!

	switch x := a.x.(type) {
	/* case tSite:
	if _, yIsSite := b.x.(tSite); yIsSite {
		union(a, b)
	} else {
		// Swap order of arguments
		ctx.unify(b, a)
	} */
	case tFresh:
		union(a, b)
	case tPointsTo:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tPointsTo:
			union(a, b)

			if x.preps != nil {
				if y.preps == nil {
					y.preps = x.preps
				} else if len(x.preps) < len(y.preps) {
					y.preps = append(y.preps, x.preps...)
				} else {
					y.preps = append(x.preps, y.preps...)
				}

				b.x = y
			}

			ctx.unify(x.x, y.x)
		default:
			panic(unificationError(x, y))
		}
	case tChan:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tChan:
			union(a, b)
			ctx.unify(x.payload, y.payload)
		default:
			panic(unificationError(x, y))
		}
	case tArray:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tArray:
			union(a, b)
			ctx.unify(x.x, y.x)
		default:
			panic(unificationError(x, y))
		}
	case tMap:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tMap:
			union(a, b)
			ctx.unify(x.keys, y.keys)
			ctx.unify(x.values, y.values)
		default:
			panic(unificationError(x, y))
		}
	case tStruct:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tStruct:
			union(a, b)

			checkLen(x.fields, y.fields, "Number of struct fields don't match")

			for i, f := range x.fields {
				ctx.unify(f, y.fields[i])
			}
		default:
			panic(unificationError(x, y))
		}
	case tClosure:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tClosure:
			union(a, b)

			// Defers are abused here to avoid reentrancy issues
			discover := x.called || y.called
			if discover {
				yCalled := y.called
				y.called = discover

				if x.called {
					// Unify args
					if yCalled {
						checkLen(x.args, y.args, "Argument lengths don't match")

						for i, a := range x.args {
							defer ctx.unify(a, y.args[i])
						}
					} else {
						y.args = x.args
					}
				}

				// We may have modified y, but y isn't a reference to the field
				// inside its term, so to preserve the changes we have to
				// reassign it.
				b.x = y

				if !yCalled {
					// Call functions that were stored in y
					for fun, fvs := range y.funs {
						defer ctx.call(fun, y.args, fvs, y.rval)
					}
				}
			}

			// Merge functions from x to y
			for fun, fvs := range x.funs {
				if ofvs, found := y.funs[fun]; found {
					for i, fv := range fvs {
						defer ctx.unify(fv, ofvs[i])
					}
				} else {
					y.funs[fun] = fvs

					if !x.called && discover {
						defer ctx.call(fun, y.args, fvs, x.rval)
					}
				}
			}

			// Unify return values
			ctx.unify(x.rval, y.rval)

		default:
			panic(unificationError(x, y))
		}
	case tInterface:
		switch y := b.x.(type) {
		case tFresh:
			union(b, a)
		case tInterface:
			if x.contents.Len() > y.contents.Len() {
				x, y = y, x
				union(b, a)
			} else {
				union(a, b)
			}

			// xContents := make(map[types.Type]*term, x.contents.Len())
			sharedContents := make(map[types.Type]*term)

			// Merge interface values from x to y
			x.contents.Iterate(func(key types.Type, v1 *term) {
				if y.contents.Has(key) {
					sharedContents[key] = v1
				} else {
					// xContents[key] = v1
					y.contents.Set(key, v1)
				}
			})

			doCalls := func(mth *types.Func, mterm method, i tInterface) {
				i.iterateCallees(ctx.config.Program, mth, func(fun *ssa.Function, recv *term) {
					ctx.call(fun, append([]*term{recv}, mterm.args...), nil, mterm.rval)
				})
			}

			// Abuse defers as for closures while merging called methods
			for mth, mterm := range x.calledMethods {
				if omterm, found := y.calledMethods[mth]; found {
					checkLen(mterm.args, omterm.args, "Argument lengths don't match")

					for i, a := range mterm.args {
						defer ctx.unify(a, omterm.args[i])
					}

					defer ctx.unify(mterm.rval, omterm.rval)
				} else {
					y.calledMethods[mth] = mterm
					defer doCalls(mth, mterm, y)
				}
			}
			// At this point we can safely call unify recursively

			// Process delayed unifications for shared contents
			for key, v1 := range sharedContents {
				ctx.unify(v1, y.contents.At(key))
			}

			// Call relevant functions on contents in x
			for mth, mterm := range y.calledMethods {
				// If the call already existed in x, we don't have to process it.
				if _, found := x.calledMethods[mth]; found {
					continue
				}

				doCalls(mth, mterm, x)
			}
		default:
			panic(unificationError(x, y))
		}
	default:
		log.Panicf("Unification of %T not implemented", x)
	}
}

// sterm returns the term containing the constraint variable for the given ssa
// value. The constructed terms are memoized in a map.
func (ctx *aContext) sterm(site ssa.Value) *term {
	if term, found := ctx.varToTerm[site]; found {
		return term
	}

	term := mkFresh()
	ctx.varToTerm[site] = term
	return term
}

var mkFresh = func() func() *term {
	var cntr int
	return func() *term {
		cntr++
		return t(tFresh{index: cntr})
	}
}()

func (ctx *aContext) zeroTermForType(t types.Type) termTag {
	switch t := t.Underlying().(type) {
	case *types.Struct:
		fields := make([]*term, t.NumFields())
		for i := range fields {
			fields[i] = mkFresh()
		}
		return tStruct{fields: fields}
	case *types.Tuple:
		fields := make([]*term, t.Len())
		for i := range fields {
			fields[i] = mkFresh()
		}
		return tStruct{fields: fields}

	case *types.Interface:
		m := &typemap[*term]{}
		m.SetHasher(ctx.tHasher)
		return tInterface{
			contents:      m,
			calledMethods: make(map[*types.Func]method),
		}

	default:
		panic(ErrNotImplemented)
	}
}
