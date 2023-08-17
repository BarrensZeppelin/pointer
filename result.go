package pointer

import (
	"fmt"
	"log"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
)

// Result exposes some public members and an API to query analysis results.
type Result struct {
	// Reachable contains all function discovered during analysis.
	Reachable map[*ssa.Function]bool
	CallGraph *callgraph.Graph

	ctx *aContext

	// Map from terms of PointsTo type to resolved labels.
	resolvedPointers map[*Term][]Label
}

// Pointer retrieves the abstract pointer associated with the given ssa Value.
func (r *Result) Pointer(v ssa.Value) Pointer {
	if !PointerLike(v.Type()) {
		panic(fmt.Errorf("the type of %v is not pointer-like", v))
	}

	return Pointer{r, find(r.ctx.eval(v))}
}

// A Pointer is an equivalence class of pointer-like values.
type Pointer struct {
	res  *Result
	term *Term
}

// MayAlias reports, in constant time, whether the receiver pointer may alias
// the argument pointer.
func (p Pointer) MayAlias(o Pointer) bool {
	_, isPtr := p.term.x.(PointsTo)
	return isPtr && p.term == o.term
}

// PointsTo returns a set of labels representing objects that the pointer may
// point to.
func (p Pointer) PointsTo() []Label {
	return p.res.resolve(p.term)
}

// resolve caches the result of computing the pointed-to labels for a pointer.
func (res *Result) resolve(t *Term) []Label {
	if resolved, found := res.resolvedPointers[t]; found {
		return resolved
	}

	switch it := t.x.(type) {
	case PointsTo:
		var labels []Label
		handledAccesses := make(map[prePTag]bool)
		for _, preP := range it.preps {
			var lab Label
			switch preP := preP.(type) {
			case prePSite:
				lab = AllocationSite{preP.site}
			case prePAccess:
				preP.base = find(preP.base)
				// Prevent duplicates by making sure that we only handle each
				// base/field combination once.
				if !handledAccesses[preP] {
					handledAccesses[preP] = true

					// For each object pointed to by the base pointer, add a
					// label representing an access on that object.
					for _, baseLabel := range res.resolve(preP.base) {
						if preP.field == -1 {
							labels = append(labels, ElementPointer{baseLabel})
						} else {
							labels = append(labels, FieldPointer{baseLabel, preP.field})
						}
					}
				}

				continue
			default:
				log.Fatalf("Unhandled pre-pointer: %T %+v", preP, preP)
			}

			if !handledAccesses[preP] {
				handledAccesses[preP] = true
				labels = append(labels, lab)
			}
		}

		res.resolvedPointers[t] = labels
		return labels
	case Closure:
		ret := make([]Label, 0, len(it.funs))
		for fun := range it.funs {
			ret = append(ret, AllocationSite{fun})
		}
		return ret
	default:
		return nil
	}
}

func (ctx *aContext) result(callgraph *callgraph.Graph) Result {
	return Result{
		Reachable: ctx.visited,
		CallGraph: callgraph,

		ctx: &aContext{
			varToTerm: ctx.varToTerm,
		},
		resolvedPointers: make(map[*Term][]Label),
	}
}
