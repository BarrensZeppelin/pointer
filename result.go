package pointer

import (
	"fmt"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
)

type Result struct {
	Reachable map[*ssa.Function]bool
	CallGraph *callgraph.Graph

	children  map[*Term][]Site
	varToTerm map[Site]*Term
}

type Pointer struct {
	res  *Result
	term *Term
}

func (r *Result) Pointer(v ssa.Value) *Pointer {
	if !PointerLike(v.Type()) {
		panic(fmt.Errorf("The type of %v is not pointer-like", v))
	}

	s, ok := r.varToTerm[Site{Value: v, Register: true}]
	if !ok {
		return &Pointer{r, mkFresh()}
	}

	return &Pointer{r, s}
}

func (p *Pointer) MayAlias(o *Pointer) bool {
	if p, ok := find(p.term).x.(PointsTo); ok {
		if p2, ok := find(o.term).x.(PointsTo); ok {
			return find(p.x) == find(p2.x)
		}
	}

	return false
}

func (p *Pointer) PointsTo() []ssa.Value {
	switch t := find(p.term).x.(type) {
	case PointsTo:
		ch := p.res.children[find(t.x)]
		r := make([]ssa.Value, len(ch))
		for i, s := range ch {
			r[i] = s.Value
		}
		return r
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
	children := map[*Term][]Site{}
	for site, term := range ctx.varToTerm {
		if !site.Register {
			term = find(term)
			children[term] = append(children[term], site)
		}
	}

	return Result{
		Reachable: ctx.visited,
		CallGraph: callgraph,

		children:  children,
		varToTerm: ctx.varToTerm,
	}
}
