package pointer_test

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"github.com/BarrensZeppelin/pointer/slices"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/packages"
	gopointer "golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

func PPValue(v ssa.Value) string {
	return fmt.Sprintf("%v: %s = %v", v.Parent(), v.Name(), v)
}

func PPSet(l []ssa.Value) string {
	return "[" + strings.Join(slices.Map(l, PPValue), ", ") + "]"
}

func checkSoundness(t *testing.T, prog *ssa.Program) {
	ptres := pointer.Analyze(pointer.AnalysisConfig{
		Program:             prog,
		TreatMethodsAsRoots: true,
	})
	cg := ptres.CallGraph

	pconfig := &gopointer.Config{
		Mains:          ssautil.MainPackages(prog.AllPackages()),
		BuildCallGraph: true,
	}

	for fun := range ssautil.AllFunctions(prog) {
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
		if _, found := cg.Nodes[reg.Parent()]; !found {
			continue
		}

		pset := ptres.Pointer(reg).PointsTo()
		pmap := make(map[ssa.Value]struct{}, len(pset))
		for _, p := range pset {
			pmap[p] = struct{}{}
		}

		flattened := []ssa.Value{}
		for _, label := range ptset.PointsTo().Labels() {
			// TODO: Our ptsto function doesn't work for subelements yet...
			if v := label.Value(); v != nil && label.Path() == "" {
				if _, reachable := cg.Nodes[v.Parent()]; reachable {
					flattened = append(flattened, v)
				}
			}
		}

		var missing []ssa.Value
		for _, p := range flattened {
			if _, found := pmap[p]; !found {
				missing = append(missing, p)
			}
		}

		if len(missing) != 0 {
			t.Errorf("%s:\n%s\n⊈\n%s", PPValue(reg), PPSet(flattened), PPSet(pset))
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
			Program: prog,
		})
		x, y := ptres.Pointer(allocs[0]), ptres.Pointer(allocs[1])

		assert.Len(t, slices.Map(x.PointsTo(), PPValue), 1,
			"x should only point to one allocation site")
		assert.Len(t, slices.Map(y.PointsTo(), PPValue), 1,
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
		Mode:  packages.LoadAllSyntax,
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
