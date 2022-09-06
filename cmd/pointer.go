package main

import (
	"log"
	"os"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

func main() {
	dir := os.Args[1]
	query := os.Args[2]

	pkgs, err := pkgutil.LoadPackagesWithConfig(&packages.Config{
		Mode:  packages.LoadAllSyntax,
		Tests: true,
		Dir:   dir,
	}, query)

	if err != nil {
		log.Fatalf("Loading packages failed: %v", err)
	}

	log.Printf("Loaded %d packages", len(pkgs))

	prog, _ := ssautil.AllPackages(pkgs, ssa.InstantiateGenerics)
	prog.Build()

	log.Println("Built packages")

	_, cg := pointer.Analyze(pointer.AnalysisConfig{
		Program: prog,
	})

	log.Printf("%d reachable functions", len(cg.Nodes))
}
