package pointer_test

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"os/exec"
	"path"
	"regexp"
	"strings"
	"testing"

	"github.com/BarrensZeppelin/pointer"
	"github.com/BarrensZeppelin/pointer/internal/slices"
	"github.com/BarrensZeppelin/pointer/pkgutil"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/expect"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"golang.org/x/tools/go/types/typeutil"
)

func TestGoPointerTests(t *testing.T) {
	cmd := exec.Command("go", "list", "-f", "{{.Dir}}", "golang.org/x/tools/go/pointer/testdata")
	var out strings.Builder
	cmd.Stdout = &out

	err := cmd.Run()
	require.NoError(t, err)

	testdataPath := strings.TrimRight(out.String(), "\n")
	testfiles, err := os.ReadDir(testdataPath)
	require.NoError(t, err)

	re := regexp.MustCompile(`(?m)// @(\w+)(?: ([^\n"]+))?$`)

	knownOverapproximations := map[string][]int{
		"arrays_go117.go": {
			57, // assignment is bidirectional
			65,
			72,  // same with copy
			111, // creating a copy of an array through dereference is bidirectional
			112,
		},
		"arrays.go": {
			54,
			62,
			69,
		},
		"channels.go": {
			41, 44, // assignment is bidirectional
		},
		"context.go": {
			20, 21, // no context sensitivity
			29, 30,
			39, 42,
		},
		"finalizer.go": {
			6, // runtime.SetFinalizer is not handled context-sensitively
			11,
			61,
		},
		"fmtexcerpt.go": {
			32, // known (fixable) imprecision in TypeAssert with interfaces
		},
		"func.go": {
			28, // return bidirectional
		},
		"maps.go": {
			45, 46, // assignment to slice contents is bidirectional
		},
		"interfaces.go": {
			39, 42, // assignment to k is bidirectional
			97, 101, 105, // known (fixable) imprecision in TypeAssert with interfaces
		},
	}

	for _, entry := range testfiles {
		overapproximations := knownOverapproximations[entry.Name()]
		fullpath := path.Join(testdataPath, entry.Name())

		config := &packages.Config{
			Mode:  pkgutil.LoadMode,
			Tests: true,
			ParseFile: func(fset *token.FileSet, filename string, src []byte) (*ast.File, error) {
				if filename == fullpath {
					src = re.ReplaceAll(src, []byte("//@ $1(\"$2\")"))
					// t.Log(filename, string(src))
				}
				return parser.ParseFile(fset, filename, src, parser.AllErrors|parser.ParseComments)
			},
		}

		entry := entry
		t.Run(entry.Name(), func(t *testing.T) {
			t.Parallel()

			pkgs, err := pkgutil.LoadPackagesWithConfig(config, fullpath)
			require.NoError(t, err)

			mainPkgIndex := 0
			if entry.Name() == "a_test.go" {
				require.Len(t, pkgs, 3)

				for i, pkg := range pkgs {
					if pkg.Name == "a" {
						mainPkgIndex = i
					}
				}
			} else {
				require.Len(t, pkgs, 1)
			}

			mainPkg := pkgs[mainPkgIndex]

			if _, found := mainPkg.Imports["reflect"]; found {
				t.Skipf("%s uses reflection", entry.Name())
			}

			prog, spkgs := ssautil.AllPackages(pkgs, ssa.InstantiateGenerics)
			require.Condition(t, func() bool {
				for _, spkg := range spkgs {
					if spkg.Func("main") != nil {
						return true
					}
				}

				return false
			}, "No main function")

			prog.Build()

			ptres := pointer.Analyze(pointer.AnalysisConfig{
				Program:       prog,
				EntryPackages: spkgs,
			})

			if entry.Name() == "issue9002.go" {
				// no notes
				return
			}

			require.Len(t, mainPkg.Syntax, 1)
			notes, err := expect.ExtractGo(prog.Fset, mainPkg.Syntax[0])
			require.NoError(t, err)
			require.NotEmpty(t, notes)

			mainFile := prog.Fset.File(mainPkg.Syntax[0].Pos())

			printArgs := map[int][]ssa.Value{}
			// for fn := range ptres.Reachable {
			for fn := range ssautil.AllFunctions(prog) {
				if isGenericBody(fn) {
					continue // skip generic bodies
				}

				if fn.Pkg == spkgs[mainPkgIndex] ||
					(fn.Pkg == nil && prog.Fset.File(fn.Pos()) == mainFile) {
					for _, block := range fn.Blocks {
						for _, insn := range block.Instrs {
							call, ok := insn.(ssa.CallInstruction)
							if !ok {
								continue
							}

							common := call.Common()
							if v, isBuiltin := common.Value.(*ssa.Builtin); isBuiltin &&
								!common.IsInvoke() && v.Name() == "print" &&
								len(common.Args) == 1 {

								pos := prog.Fset.Position(insn.Pos())
								printArgs[pos.Line] = append(printArgs[pos.Line], common.Args[0])
							}
						}
					}
				}
			}

			lineMapping := map[string]string{}
			for _, note := range notes {
				pos := prog.Fset.Position(note.Pos)
				arg := note.Args[0].(string)

				if note.Name == "line" {
					lineMapping[fmt.Sprintf("%s:%d", pos.Filename, pos.Line)] = arg
				}
			}

			for _, note := range notes {
				pos := prog.Fset.Position(note.Pos)
				pos.Filename = strings.TrimPrefix(pos.Filename,
					testdataPath+string(os.PathSeparator))
				arg := note.Args[0].(string)

				exact := !slices.Contains(overapproximations, pos.Line)

				switch note.Name {
				case "pointsto":
					var expected, actual []string
					if arg != "" {
						for _, g := range strings.Split(arg, " | ") {
							if g == "..." {
								exact = false
								continue
							}
							expected = append(expected, g)
						}
					}

					pa := printArgs[pos.Line]
					require.NotNil(t, pa)

					for _, v := range pa {
						for _, label := range ptres.Pointer(v).PointsTo() {
							name := labelString(label, lineMapping, prog)
							actual = append(actual, name)
						}
					}

					if exact {
						assert.ElementsMatchf(t, actual, expected, "At %v", pos)
					} else {
						assert.Subsetf(t, actual, expected, "At %v", pos)

						if !slices.Contains(expected, "<command-line args>") {
							assert.NotSubsetf(t, expected, actual,
								"Assertion at %v should be exact", pos)
						}
					}

				case "types":
					var expected typeutil.Map
					if arg != "" {
						for _, typstr := range strings.Split(arg, " | ") {
							if typstr == "..." {
								exact = false
							} else {
								tv, err := types.Eval(prog.Fset, spkgs[0].Pkg, mainPkg.Syntax[0].Pos(), typstr)
								if assert.NoError(t, err, "'%s' is not a valid type", typstr) {
									expected.Set(tv.Type, struct{}{})
								}
							}

						}
					}

					pa := printArgs[pos.Line]
					require.NotNil(t, pa)

					var actual typeutil.Map
					for _, v := range pa {
						if types.IsInterface(v.Type()) {
							ptres.DynamicTypes(v).Iterate(func(k types.Type, _ any) {
								actual.Set(k, struct{}{})
							})
						} else {
							actual.Set(v.Type(), struct{}{})
						}
					}

					var extra []types.Type
					actual.Iterate(func(t types.Type, _ any) {
						if !expected.Delete(t) {
							extra = append(extra, t)
						}
					})

					assert.Emptyf(t, expected.Keys(), "Actual types: %v\nAt %v", actual.KeysString(), pos)

					if exact {
						assert.Emptyf(t, extra, "Additional types %v at %v", extra, pos)
					} else {
						assert.NotEmptyf(t, extra, "Assertion at %v should be exact", pos)
					}
				}
			}
		})
	}
}

// isGenericBody returns true if fn is the body of a generic function.
func isGenericBody(fn *ssa.Function) bool {
	sig := fn.Signature
	if sig.TypeParams().Len() > 0 || sig.RecvTypeParams().Len() > 0 {
		return fn.Synthetic == ""
	}
	return false
}

func labelString(l pointer.Label, lineMapping map[string]string, prog *ssa.Program) string {
	if s, ok := l.(pointer.Synthetic); ok {
		return s.Label
	}

	s := l.Site()

	str := func() string {
		switch v := s.(type) {
		case *ssa.Function, *ssa.Global:
			return v.String()

		case *ssa.Const:
			return v.Name()

		case *ssa.Alloc:
			if v.Comment != "" {
				return v.Comment
			}

			return "alloc"

		case *ssa.Call:
			// Currently only calls to append can allocate objects.
			if v.Call.Value.(*ssa.Builtin).Object().Name() != "append" {
				panic("unhandled *ssa.Call label: " + v.Name())
			}
			return "append"

		case *ssa.MakeMap, *ssa.MakeChan, *ssa.MakeSlice, *ssa.Convert:
			return strings.ToLower(strings.TrimPrefix(fmt.Sprintf("%T", v), "*ssa."))

		case *ssa.MakeInterface:
			// MakeInterface is usually implicit in Go source (so
			// Pos()==0), and tagged objects may be allocated
			// synthetically (so no *MakeInterface data).
			return "makeinterface:" + v.X.Type().String()

		default:
			panic(fmt.Sprintf("unhandled object data type: %T", v))
		}
	}() + l.Path()

	// Functions and Globals need no pos suffix,
	// nor do allocations in intrinsic operations
	// (for which we'll print the function name).
	switch s.(type) {
	case *ssa.Function, *ssa.Global:
		return str
	}

	if pos := s.Pos(); pos != token.NoPos {
		// Append the position, using a @line tag instead of a line number, if defined.
		posn := prog.Fset.Position(pos)
		s := fmt.Sprintf("%s:%d", posn.Filename, posn.Line)
		if tag, ok := lineMapping[s]; ok {
			return fmt.Sprintf("%s@%s:%d", str, tag, posn.Column)
		}
		str = fmt.Sprintf("%s@%s", str, posn)
	}
	return str
}
