package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io/fs"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"runtime/pprof"
	"strings"
	"time"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/packages"
	gopointer "golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

var benchmarks = []repo{
	{"grpc/grpc-go", "23ac72b6454a2bcac32e19ccf501ca3a070f517c"},
	{"gin-gonic/gin", "dc9cff732e27ce4ac21b25772a83c462a28b8b80"},
	{"fatedier/frp", "f1454e91f56508603e4c2e3c7bf37ccb534458c2"},
	// kubernetes takes a long time to analyze...
	// {"kubernetes/kubernetes", "2a5fd3076aee14c1be51c703a7e5b447d638387d"},
	// {"gohugoio/hugo", "2ae4786ca1e4b912fabc8a6be503772374fed5d6"},
	// {"grafana/grafana", "85a207fcebb5acffe6474b97fef91f611f1989ee"},
	{"junegunn/fzf", "58835e40f35fd1007de9bf607e06d555f085354c"},
	// {"syncthing/syncthing", "95b3c26da724aff5b9aae88daf0783d866e95fda"},
	{"caddyserver/caddy", "1b73e3862d312ac2057265bf2a5fd95760dbe9da"},
}

var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to `file`")

var dir = "."

type repo struct{ name, commit string }

func (r repo) install() string {
	repodir := filepath.Join(dir, "_benchfiles", strings.ReplaceAll(r.name, "/", "#"))
	if _, err := os.Stat(repodir); err != nil {
		if !os.IsNotExist(err) {
			log.Fatal(err)
		}

		log.Printf("Installing %s @ %s", r.name, r.commit)

		os.MkdirAll(repodir, 0750)

		cmd := exec.Command("sh", "-c",
			fmt.Sprintf(`git init && \
	git config advice.detachedHead false && \
	git remote add origin https://github.com/%s.git && \
	git fetch --depth 1 origin %s && \
	git checkout FETCH_HEAD`, r.name, r.commit))
		cmd.Dir = repodir
		if err := cmd.Run(); err != nil {
			log.Fatal(err)
		}
	}

	return repodir
}

func main() {
	flag.Parse()

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

	dirs := make([]string, len(benchmarks))
	for i, repo := range benchmarks {
		dirs[i] = repo.install()
	}

	dataFile, err := os.Create(filepath.Join(dir, "data.jsonl"))
	if err != nil {
		log.Fatal(err)
	}
	defer func() {
		if err := dataFile.Close(); err != nil {
			log.Fatalf("Failed to close: %v %v", dataFile, err)
		}
	}()

	dataEncoder := json.NewEncoder(dataFile)

	for i, dir := range dirs {
		var modules []string
		err := filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
			if filepath.Base(path) == "go.mod" {
				modules = append(modules, path)
			}
			return nil
		})
		if err != nil {
			log.Fatal(err)
		}

		println()
		log.Printf("Found %d modules for %s", len(modules), benchmarks[i].name)

		for _, mod := range modules {
			gopath, err := filepath.Abs(filepath.Dir(dir))
			if err != nil {
				log.Fatal(err)
			}

			println()
			moddir := filepath.Dir(mod)
			pkgs, err := pkgutil.LoadPackagesWithConfig(&packages.Config{
				Mode:  pkgutil.LoadMode | packages.NeedModule,
				Tests: true,
				Dir:   moddir,
				Env:   append(os.Environ(), "GO111MODULE=on", "GOPATH="+gopath),
			}, "./...")
			if err != nil {
				log.Print(moddir, err)
				continue
			}

			if len(pkgs) == 0 {
				log.Printf("Skipping module at %v as it has no packages", mod)
				continue
			}

			modulePath := pkgs[0].Module.Path
			log.Printf("Loaded %d packages for %s", len(pkgs), modulePath)

			var mainPkgs []*packages.Package
			for _, pkg := range pkgs {
				if pkg.Name == "main" {
					mainPkgs = append(mainPkgs, pkg)
				}
			}

			data := map[string]any{
				"module":       modulePath,
				"packages":     len(pkgs),
				"mainPackages": len(mainPkgs),
			}

			prog, _ := ssautil.AllPackages(mainPkgs, ssa.InstantiateGenerics)
			prog.Build()

			log.Print("SSA construction complete")
			ssaMains := ssautil.MainPackages(prog.AllPackages())
			if len(ssaMains) == 0 {
				log.Print("Skipping due to no main packages")
				continue
			}

			start := time.Now()
			res := pointer.Analyze(pointer.AnalysisConfig{
				Program:       prog,
				EntryPackages: ssaMains,
			})
			analysisDuration := time.Since(start)
			log.Printf(`Steensgaard analysis completed in %v
Reachable functions: %d`, analysisDuration, len(res.Reachable))

			start = time.Now()
			cg := res.CallGraph()
			callGraphDuration := time.Since(start)
			log.Printf("Constructed call graph in %v", callGraphDuration)

			callGraphEdges, calleeCount := callGraphStats(cg, res.Reachable)
			log.Printf("Call graph edges: %d", callGraphEdges)

			aconfig := &gopointer.Config{Mains: ssaMains, BuildCallGraph: true}
			for fun := range res.Reachable {
				addQueries(fun, aconfig)
			}

			start = time.Now()
			var precision int
			for v := range aconfig.Queries {
				precision += len(res.Pointer(v).PointsTo())
			}
			queryDuration := time.Since(start)
			log.Printf("Queries completed in %v\nPrecision: %d", queryDuration, precision)

			if r := getReachable(cg); len(r) != len(res.Reachable)+1 {
				log.Fatalf("What? %d != %d", len(r), len(res.Reachable)+1)
			}

			data["steensgaard"] = map[string]any{
				"analysisDuration":  analysisDuration.Milliseconds(),
				"callGraphDuration": callGraphDuration.Milliseconds(),
				"reachable":         len(res.Reachable),
				"queryDuration":     queryDuration.Milliseconds(),
				"precision":         precision,
				"callGraphEdges":    callGraphEdges,
				"calleeCount":       calleeCount,
			}

			start = time.Now()
			gores, err := gopointer.Analyze(aconfig)
			if err != nil {
				log.Fatal("Go pointer analysis crashed: ", err)
			}
			analysisDuration = time.Since(start)
			log.Printf(`Andersen analysis completed in %v`, analysisDuration)

			r2 := getReachable(gores.CallGraph)
			log.Printf("Reachable functions: %d (%.2f%%)",
				len(r2), float64(len(r2)*100)/float64(len(res.Reachable)))

			callGraphEdges2, calleeCount2 := callGraphStats(gores.CallGraph, r2)
			log.Printf("Call graph edges: %d (%.2f%%)",
				callGraphEdges2, float64(callGraphEdges2*100)/float64(callGraphEdges))

			start = time.Now()
			var precision2 int
			for _, pt := range gores.Queries {
				precision2 += len(pt.PointsTo().Labels())
			}
			queryDuration = time.Since(start)
			log.Printf("Queries completed in %v\nPrecision: %d (%.2f%%)",
				queryDuration, precision2, float64(precision2*100)/float64(precision))

			data["andersen"] = map[string]any{
				"analysisDuration": analysisDuration.Milliseconds(),
				"reachable":        len(r2),
				"queryDuration":    queryDuration.Milliseconds(),
				"precision":        precision2,
				"callGraphEdges":   callGraphEdges2,
				"calleeCount":      calleeCount2,
			}

			dataEncoder.Encode(data)
		}
	}
}

func addQueries(fun *ssa.Function, pconfig *gopointer.Config) {
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

func getReachable(cg *callgraph.Graph) map[*ssa.Function]bool {
	V := map[*callgraph.Node]bool{cg.Root: true}
	Q := []*callgraph.Node{cg.Root}
	for len(Q) > 0 {
		i := Q[0]
		Q = Q[1:]

		for _, edge := range i.Out {
			j := edge.Callee
			if !V[j] {
				V[j] = true
				Q = append(Q, j)
			}
		}
	}

	res := map[*ssa.Function]bool{}
	for node := range V {
		if node.Func != nil {
			res[node.Func] = true
		}
	}
	return res
}

func callGraphStats(cg *callgraph.Graph, funs map[*ssa.Function]bool) (
	total int,
	calleeCount map[int]int,
) {
	calleeCount = make(map[int]int)

	for fun := range funs {
		node := cg.Nodes[fun]
		if node != nil {
			ccnt := map[ssa.CallInstruction]int{}
			for _, edge := range node.Out {
				if edge.Site == nil || edge.Site.Common().StaticCallee() != nil {
					continue
				}

				total++
				ccnt[edge.Site]++
			}

			for _, cnt := range ccnt {
				calleeCount[cnt]++
			}
		}
	}
	return
}
