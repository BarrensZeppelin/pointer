package main

import (
	"flag"
	"log"
	"os"
	"runtime/pprof"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to `file`")
var dir = flag.String("dir", "", "alternative directory to run the go build tool in")

func main() {
	flag.Parse()

	if flag.NArg() == 0 {
		log.Fatal("Specify a package query on the command line")
	}

	if *cpuprofile != "" {
		f, err := os.Create(*cpuprofile)
		if err != nil {
			log.Fatal("could not create CPU profile: ", err)
		}
		defer func() {
			if err := f.Close(); err != nil {
				log.Fatal("Failed to close", f)
			}
		}()
		if err := pprof.StartCPUProfile(f); err != nil {
			log.Fatal("could not start CPU profile: ", err)
		}
		defer pprof.StopCPUProfile()
	}

	pkgs, err := pkgutil.LoadPackagesWithConfig(&packages.Config{
		Mode:  pkgutil.LoadMode,
		Tests: true,
		Dir:   *dir,
	}, flag.Args()...)

	if err != nil {
		log.Fatalf("Loading packages failed: %v", err)
	}

	log.Printf("Loaded %d packages", len(pkgs))

	prog, _ := ssautil.AllPackages(pkgs, ssa.InstantiateGenerics)
	prog.Build()

	log.Println("Built packages")

	res := pointer.Analyze(pointer.AnalysisConfig{
		Program: prog,
		EntryPackages: ssautil.MainPackages(prog.AllPackages()),
	})

	log.Printf("%d reachable functions", len(res.Reachable))
}
