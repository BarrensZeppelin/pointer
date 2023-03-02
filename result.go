package pointer

import (
	"fmt"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
)

type Result struct {
	Reachable map[*ssa.Function]bool
	CallGraph *callgraph.Graph

	varToTerm map[ssa.Value]*Term
}

type Pointer struct {
	res  *Result
	term *Term
}

func (r *Result) Pointer(v ssa.Value) *Pointer {
	if !PointerLike(v.Type()) {
		panic(fmt.Errorf("The type of %v is not pointer-like", v))
	}

	s, ok := r.varToTerm[v]
	if !ok {
		return &Pointer{r, mkFresh()}
	}

	return &Pointer{r, find(s)}
}

func (p *Pointer) MayAlias(o *Pointer) bool {
	_, isPtr := p.term.x.(PointsTo)
	return isPtr && p.term == o.term
}

func (p *Pointer) PointsTo() []ssa.Value {
	switch t := find(p.term).x.(type) {
	case PointsTo:
		return t.sites
	case Closure:
		ret := make([]ssa.Value, 0, len(t.funs))
		for fun := range t.funs {
			ret = append(ret, fun)
		}
		return ret
	default:
		return nil
	}
}

func (ctx *aContext) result(callgraph *callgraph.Graph) Result {
	/* children := map[*Term][]Site{}
	for site, term := range ctx.varToTerm {
		if !site.Register {
			term = find(term)
			children[term] = append(children[term], site)
		}
	} */

	return Result{
		Reachable: ctx.visited,
		CallGraph: callgraph,

		varToTerm: ctx.varToTerm,
	}
}
