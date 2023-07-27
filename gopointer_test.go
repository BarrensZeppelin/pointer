package pointer_test

import (
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

	for _, entry := range testfiles {
		if entry.Name() == "a_test.go" || strings.Contains(entry.Name(), "reflect") {
			continue
		}

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
			// t.Parallel()

			pkgs, err := pkgutil.LoadPackagesWithConfig(config, fullpath)
			require.NoError(t, err)
			require.Len(t, pkgs, 1)

			prog, spkgs := ssautil.AllPackages(pkgs, ssa.InstantiateGenerics)
			require.NotNil(t, spkgs[0].Func("main"), "No main function")

			prog.Build()

			ptres := pointer.Analyze(pointer.AnalysisConfig{
				Program:       prog,
				EntryPackages: spkgs,
			})

			require.Len(t, pkgs[0].Syntax, 1)
			notes, err := expect.ExtractGo(prog.Fset, pkgs[0].Syntax[0])
			require.NoError(t, err)

			mainPkg := pkgs[0]
			mainFiles := make(map[*token.File]bool)
			for _, syn := range mainPkg.Syntax {
				mainFiles[prog.Fset.File(syn.Pos())] = true
			}

			printArgs := map[int][]ssa.Value{}
			// for fn := range ptres.Reachable {
			for fn := range ssautil.AllFunctions(prog) {
				if isGenericBody(fn) {
					continue // skip generic bodies
				}

				if fn.Pkg == spkgs[0] || (fn.Pkg == nil && mainFiles[prog.Fset.File(fn.Pos())]) {
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

			// TODO: Line mappings

			for _, note := range notes {
				pos := prog.Fset.Position(note.Pos)
				arg := note.Args[0].(string)

				switch note.Name {
				case "types":
					var expected typeutil.Map
					exact := false
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
						assert.Empty(t, extra)
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
