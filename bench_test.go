package pointer_test

import (
	"fmt"
	"testing"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

var blackHole any

// Benchmark performance of pointer analysis (and callgraph construction) on
// the standard library (w. tests)
func BenchmarkStdlibAnalysis(b *testing.B) {
	pkgs, err := pkgutil.LoadPackagesWithConfig(
		&packages.Config{
			Mode:  pkgutil.LoadMode,
			Tests: true,
			Dir:   "",
		}, "std")
	require.NoError(b, err)

	prog, spkgs := ssautil.AllPackages(pkgs, ssa.InstantiateGenerics)
	prog.Build()

	mains := ssautil.MainPackages(spkgs)

	for _, methodsAreRoots := range [...]bool{false, true} {
		b.Run(fmt.Sprintf("Steensgaard(MethodsAreRoots=%v)", methodsAreRoots),
			func(b *testing.B) {
				blackHole = pointer.Analyze(pointer.AnalysisConfig{
					Program:             prog,
					EntryPackages:       mains,
					TreatMethodsAsRoots: methodsAreRoots,
				})
			})
	}
}
