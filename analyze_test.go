package pointer_test

import (
	"fmt"
	"log"
	"os"
	"path/filepath"
	"testing"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/internal/maps"
	"github.com/BarrensZeppelin/pointer/internal/slices"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/packages"
	gopointer "golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

func init() {
	// Set up logging
	log.SetFlags(log.Ltime | log.Lshortfile)
}

// PPValue pretty-prints the given value.
func PPValue(v ssa.Value) string {
	return fmt.Sprintf("%v: %s = %v", v.Parent(), v.Name(), v)
}

// compPtr is a common format for comparing pointers returned from pointer
// analyses. It contains the allocation site and access path.
type compPtr struct {
	site ssa.Value
	path string
}

func (cp compPtr) String() string {
	return PPValue(cp.site) + cp.path
}

// toCompPtrs extract a list of compPtrs from the points-to relation of the
// steensgaard analysis.
func toCompPtrs(p pointer.Pointer) []compPtr {
	pset := p.PointsTo()
	res := make([]compPtr, len(pset))
	for i, p := range pset {
		res[i] = compPtr{p.Site(), p.Path()}
	}
	return res
}

// andersenToCompPtrs extract a list of compPtrs from the points-to relation of
// the andersen analysis. Only pointers to objects with reachable allocation
// sites are returned.
func andersenToCompPtrs(p gopointer.Pointer, reachable map[*ssa.Function]bool) []compPtr {
	labels := p.PointsTo().Labels()
	res := make([]compPtr, 0, len(labels))
	for _, label := range labels {
		if v := label.Value(); v != nil && reachable[v.Parent()] {
			res = append(res, compPtr{v, label.Path()})
		}
	}
	return res
}

func checkSoundness(t *testing.T, prog *ssa.Program) {
	mains := ssautil.MainPackages(prog.AllPackages())
	ptres := pointer.Analyze(pointer.AnalysisConfig{
		Program:             prog,
		EntryPackages:       mains,
		TreatMethodsAsRoots: true,
	})
	cg := ptres.CallGraph

	pconfig := &gopointer.Config{
		Mains:          mains,
		BuildCallGraph: true,
	}

	for fun := range ptres.Reachable {
		for _, param := range fun.Params {
			if pointer.PointerLike(param.Type()) {
				pconfig.AddQuery(param)
			}
		}

		for _, fv := range fun.FreeVars {
			if pointer.PointerLike(fv.Type()) {
				pconfig.AddQuery(fv)
			}
		}

		for _, block := range fun.Blocks {
			for _, insn := range block.Instrs {
				switch val := insn.(type) {
				case *ssa.Range: // has degenerate type
				case ssa.Value:
					if pointer.PointerLike(val.Type()) {
						pconfig.AddQuery(val)
					}
				}
			}
		}
	}

	res, err := gopointer.Analyze(pconfig)
	if err != nil {
		t.Fatal(err)
	}

	eds := func(n *callgraph.Node) map[ssa.CallInstruction][]*ssa.Function {
		ret := map[ssa.CallInstruction][]*ssa.Function{}
		for _, out := range n.Out {
			ret[out.Site] = append(ret[out.Site], out.Callee.Func)
		}
		return ret
	}

	for fun, n1 := range cg.Nodes {
		if n2, found := res.CallGraph.Nodes[fun]; found {
			e1, e2 := eds(n1), eds(n2)
			for site, out := range e2 {
				// Go's pointer analysis has an annoying specialization of
				// invokes to methods on reflect.Type, which means that a call
				// is generated even when the points-to set of the receiver is
				// empty...
				if site != nil && site.Common().IsInvoke() &&
					res.Queries[site.Common().Value].DynamicTypes().Len() == 0 {
					continue
				}

				assert.Subset(t, e1[site], out,
					"Missing callees in %v at %v", fun, site)
			}
		}
	}

	for reg, ptset := range res.Queries {
		pmap := maps.FromKeys(toCompPtrs(ptres.Pointer(reg)))
		flattened := andersenToCompPtrs(ptset, ptres.Reachable)

		var missing []compPtr
		for _, p := range flattened {
			if _, found := pmap[p]; !found {
				missing = append(missing, p)
			}
		}

		if len(missing) != 0 {
			t.Errorf("%s:\n%s\n⊈\n%s", reg, flattened, maps.Keys(pmap))
		}
	}
}

func TestAnalyze(t *testing.T) {
	t.Run("Example", func(t *testing.T) {
		pkgs, err := pkgutil.LoadPackagesFromSource(`
			package main

			func ubool() bool

			func main() {
				x := new(*int)
				*x = new(int)
				if ubool() {
					*x = new(int)
				}
				y := *x
				*y = 10
				println(y)
			}`)

		require.Nil(t, err)

		prog, _ := ssautil.AllPackages(pkgs, ssa.SanityCheckFunctions)
		prog.Build()

		checkSoundness(t, prog)
	})

	t.Run("SpuriousPointsTo", func(t *testing.T) {
		pkgs, err := pkgutil.LoadPackagesFromSource(`
			package main
			func ubool() bool
			func main() {
				x := new(*int)
				y := new(*int)
				z := *x
				if ubool() { z = *y }
				println(z)
			}`)

		require.Nil(t, err)

		prog, spkgs := ssautil.AllPackages(pkgs, ssa.SanityCheckFunctions)
		prog.Build()

		mainPkg := spkgs[0]
		allocs := []*ssa.Alloc{}
		for _, insn := range mainPkg.Func("main").Blocks[0].Instrs {
			if alloc, ok := insn.(*ssa.Alloc); ok {
				allocs = append(allocs, alloc)
			}
		}

		require.Len(t, allocs, 2)

		ptres := pointer.Analyze(pointer.AnalysisConfig{
			Program:       prog,
			EntryPackages: spkgs,
		})
		x, y := ptres.Pointer(allocs[0]), ptres.Pointer(allocs[1])

		assert.Len(t, toCompPtrs(x), 1,
			"x should only point to one allocation site")
		assert.Len(t, toCompPtrs(y), 1,
			"y should only point to one allocation site")
		assert.False(t, x.MayAlias(y), "x and y should not alias")
	})
}

func TestGoatExamples(t *testing.T) {
	gopath, err := filepath.Abs("submodules/goat/examples")
	require.NoError(t, err)

	if _, err := os.Stat(gopath); err != nil {
		t.Skip(
			"The example programs from goat are missing. Run\n" +
				"git submodule update --init\nto clone them.")
	}

	config := &packages.Config{
		Mode:  pkgutil.LoadMode,
		Tests: true,
		Dir:   "",
		Env: append(os.Environ(), "GO111MODULE=off",
			"GOPATH="+gopath),
	}

	pkgs, err := pkgutil.LoadPackagesWithConfig(config,
		"simple-examples/...",
		"session-types-benchmarks/...",
		"gobench/goker/blocking/...",
		"sync-pkg/...",
		"sync-pkg-cond/...",
		"top-pointers/...",
	)
	require.NoError(t, err)

	blocklist := []string{
		// Andersen result is too imprecise...
		"gobench/goker/blocking/cockroach/13197",
	}

	for _, pkg := range pkgs {
		if slices.Contains(blocklist, pkg.PkgPath) {
			continue
		}

		pkg := pkg
		t.Run(pkg.PkgPath, func(t *testing.T) {
			t.Parallel()
			prog, spkgs := ssautil.AllPackages(
				[]*packages.Package{pkg},
				ssa.InstantiateGenerics)

			if spkgs[0].Func("main") == nil {
				t.Skip("No main function")
			}

			prog.Build()

			checkSoundness(t, prog)
		})
	}
}
