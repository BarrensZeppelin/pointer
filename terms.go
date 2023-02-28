package pointer

import (
	"fmt"
	"go/types"
	"log"

	"github.com/BarrensZeppelin/pointer/slices"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/types/typeutil"
)

type termTag interface{ termTag() }
type ttag struct{}

func (ttag) termTag() {}

type Fresh struct {
	ttag
	index int
}

func (f Fresh) String() string {
	return fmt.Sprintf("α%d", f.index)
}

type Site struct {
	ttag
	ssa.Value
	Register bool
}

func (s Site) String() string {
	if s.Register {
		return s.Name()
	}
	return fmt.Sprintf("%s = %v", s.Name(), s.Value.String())
}


type PointsTo struct {
	ttag
	x *Term
}

func (c PointsTo) String() string {
	return fmt.Sprintf("↑ %T", find(c.x).x)
}

type Chan struct {
	ttag
	payload *Term
}

func (c Chan) String() string {
	return fmt.Sprintf("Chan(%v)", find(c.payload))
}

type Array struct {
	ttag
	x *Term
}

func (a Array) String() string {
	return fmt.Sprintf("Array(%v)", find(a.x))
}

type Map struct {
	ttag
	keys   *Term
	values *Term
}

func (m Map) String() string {
	return fmt.Sprintf("Map(%v ↦ %v)", find(m.keys), find(m.values))
}

type Struct struct {
	ttag
	fields []*Term
}

func (s Struct) String() string {
	var inner []string
	for i, field := range s.fields {
		inner = append(inner, fmt.Sprintf("%d ↦ %v", i, find(field)))
	}
	return fmt.Sprintf("Struct(%v)", inner)
}

type Closure struct {
	ttag
	called bool
	funs   map[*ssa.Function][]*Term
	args   []*Term
	rval   *Term
}

func (c Closure) String() string {
	var inner []string
	for fun, fvs := range c.funs {
		inner = append(inner, fmt.Sprintf("%v ↦ %v", fun, slices.Map(fvs, find)))
	}
	return fmt.Sprintf("Closure(%v)", inner)
}

type method struct {
	args []*Term
	rval *Term
}

type Interface struct {
	ttag
	contents      *typeutil.Map
	calledMethods map[*types.Func]method
}

func (i Interface) String() string {
	var inner []string
	i.contents.Iterate(func(t types.Type, v any) {
		inner = append(inner, fmt.Sprintf("%v ↦ %v", t, find(v.(*Term))))
	})
	return fmt.Sprintf("Interface(%v)", inner)
}

func (i Interface) iterateCallees(
	prog *ssa.Program,
	method *types.Func,
	f func(fun *ssa.Function, recv *Term),
) {
	recv := method.Type().(*types.Signature).Recv().Type().Underlying().(*types.Interface)
	i.contents.Iterate(func(key types.Type, v any) {
		// Method lookup is only based on name, not type, so we
		// have to check whether the dynamic type implements the
		// interface first.
		if !types.Implements(key, recv) {
			return
		}

		ms := prog.MethodSets.MethodSet(key)
		if sel := ms.Lookup(method.Pkg(), method.Name()); sel != nil {
			fun := prog.MethodValue(sel)
			f(fun, v.(*Term))
		}
	})
}

type Term struct {
	x      termTag
	parent *Term
}

func (t *Term) String() string {
	return fmt.Sprint(t.x)
}

func T(x termTag) *Term {
	return &Term{x: x}
}

func find(t *Term) *Term {
	if t.parent == nil {
		return t
	}
	t.parent = find(t.parent)
	return t.parent
}

// union makes `b` the parent of `a`.
func union(a, b *Term) {
	if a.parent != nil || b.parent != nil {
		panic("union arguments should be representatives")
	}

	a.parent = b
}

func unificationError(a, b termTag) error {
	return fmt.Errorf("Unable to unify terms of type %T and %T", a, b)
}

func (ctx *aContext) discoverFun(fun *ssa.Function) {
	if !ctx.visited[fun] {
		ctx.visited[fun] = true
		ctx.queue.Push(fun)
	}
}

func (ctx *aContext) call(fun *ssa.Function, args []*Term, fvs []*Term, rval *Term) {
	ctx.discoverFun(fun)

	for i, fv := range fun.FreeVars {
		ctx.unify(ctx.eval(fv), fvs[i])
	}

	for i, a := range fun.Params {
		ctx.unify(ctx.eval(a), args[i])
	}

	for _, block := range fun.Blocks {
		if ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return); ok {
			switch len(ret.Results) {
			case 0:
			case 1:
				ctx.unify(rval, ctx.eval(ret.Results[0]))
			default:
				ctx.unify(rval, T(Struct{fields: slices.Map(ret.Results, ctx.eval)}))
			}
		}
	}
}

func checkLen[L ~[]T, T any](a, b L, msg string) {
	if len(a) != len(b) {
		log.Panicf("%s: %v (%d) != %v (%d)", msg, a, len(a), b, len(b))
	}
}

func (ctx *aContext) unify(a, b *Term) {
	a, b = find(a), find(b)
	if a == b {
		return
	}

	// Implementation here is a bit finnicky.
	// It seems it like it should be simple enough, but due to reentrancy we
	// have to make sure that the immediate effects of the current unify are
	// applied before calling unify recursively!

	switch x := a.x.(type) {
	case Site:
		if _, yIsSite := b.x.(Site); yIsSite {
			union(a, b)
		} else {
			// Swap order of arguments
			ctx.unify(b, a)
		}
	case Fresh:
		union(a, b)
	case PointsTo:
		switch y := b.x.(type) {
		case Site, Fresh:
			union(b, a)
		case PointsTo:
			union(a, b)
			ctx.unify(x.x, y.x)
		default:
			panic(unificationError(x, y))
		}
	case Chan:
		switch y := b.x.(type) {
		case Site:
			union(b, a)
		case Chan:
			union(a, b)
			ctx.unify(x.payload, y.payload)
		default:
			panic(unificationError(x, y))
		}
	case Array:
		switch y := b.x.(type) {
		case Site, Fresh:
			union(b, a)
		case Array:
			union(a, b)
			ctx.unify(x.x, y.x)
		default:
			panic(unificationError(x, y))
		}
	case Map:
		switch y := b.x.(type) {
		case Site, Fresh:
			union(b, a)
		case Map:
			union(a, b)
			ctx.unify(x.keys, y.keys)
			ctx.unify(x.values, y.values)
		default:
			panic(unificationError(x, y))
		}
	case Struct:
		switch y := b.x.(type) {
		case Site, Fresh:
			union(b, a)
		case Struct:
			union(a, b)

			checkLen(x.fields, y.fields, "Number of struct fields don't match")

			for i, f := range x.fields {
				ctx.unify(f, y.fields[i])
			}
		default:
			panic(unificationError(x, y))
		}
	case Closure:
		switch y := b.x.(type) {
		case Site, Fresh:
			union(b, a)
		case Closure:
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
	case Interface:
		switch y := b.x.(type) {
		case Site:
			union(b, a)
		case Interface:
			if x.contents.Len() > y.contents.Len() {
				x, y = y, x
				union(b, a)
			} else {
				union(a, b)
			}

			// xContents := make(map[types.Type]*Term, x.contents.Len())
			sharedContents := make(map[types.Type]*Term)

			// Merge interface values from x to y
			x.contents.Iterate(func(key types.Type, v1 any) {
				if v2 := y.contents.At(key); v2 != nil {
					sharedContents[key] = v1.(*Term)
				} else {
					// xContents[key] = v1.(*Term)
					y.contents.Set(key, v1)
				}
			})

			doCalls := func(mth *types.Func, mterm method, i Interface) {
				i.iterateCallees(ctx.prog, mth, func(fun *ssa.Function, recv *Term) {
					ctx.call(fun, append([]*Term{recv}, mterm.args...), nil, mterm.rval)
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
				ctx.unify(v1, y.contents.At(key).(*Term))
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

func (ctx *aContext) mkTerm(t Site) *Term {
	if term, found := ctx.varToTerm[t]; found {
		return term
	}
	term := T(t)
	ctx.varToTerm[t] = term
	return term
}

func (ctx *aContext) sterm(v ssa.Value, reg bool) *Term {
	site := Site{Value: v, Register: reg}
	return ctx.mkTerm(site)
}

var mkFresh = func() func() *Term {
	var cntr int
	return func() *Term {
		cntr++
		return T(Fresh{index: cntr})
	}
}()

func (ctx *aContext) zeroTermForType(t types.Type) termTag {
	switch t := t.Underlying().(type) {
	case *types.Struct:
		fields := make([]*Term, t.NumFields())
		for i := range fields {
			fields[i] = mkFresh()
		}
		return Struct{fields: fields}
	case *types.Tuple:
		fields := make([]*Term, t.Len())
		for i := range fields {
			fields[i] = mkFresh()
		}
		return Struct{fields: fields}

	case *types.Interface:
		m := &typeutil.Map{}
		m.SetHasher(ctx.tHasher)
		return Interface{
			contents:      m,
			calledMethods: make(map[*types.Func]method),
		}

	default:
		panic(ErrNotImplemented)
	}
}
