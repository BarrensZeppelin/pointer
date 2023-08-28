package pkgutil

import (
	"errors"
	"fmt"
	"os"

	"github.com/BarrensZeppelin/pointer/internal/slices"
	"golang.org/x/tools/go/packages"
)

// Should be equivalent to packages.LoadAllSyntax (which is deprecated)
const LoadMode = packages.NeedSyntax | packages.NeedTypesInfo | packages.NeedTypes |
	packages.NeedTypesSizes | packages.NeedImports | packages.NeedName |
	packages.NeedFiles | packages.NeedCompiledGoFiles | packages.NeedDeps

func LoadPackagesFromSource(source string) ([]*packages.Package, error) {
	// We use the Overlay mechanism to allow the tool to load a non-existent file.
	config := &packages.Config{
		Mode:  LoadMode,
		Tests: false,
		Dir:   "",
		Env:   append(os.Environ(), "GO111MODULE=off", "GOPATH=/fake"),
		Overlay: map[string][]byte{
			"/fake/testpackage/main.go": []byte(source),
		},
	}

	return LoadPackagesWithConfig(config, "/fake/testpackage/main.go")
}

func LoadPackagesWithConfig(config *packages.Config, queries ...string) ([]*packages.Package, error) {
	pkgs, err := packages.Load(config, queries...)
	switch {
	case err != nil:
		return nil, err
	case packages.PrintErrors(pkgs) > 0:
		return pkgs, errors.New("errors encountered while loading packages")
	default:
		if config.Tests {
			// Deduplicate packages that have test functions (such packages are
			// returned twice, once with no tests and once with tests. We discard
			// the package without tests.) This prevents duplicate versions of the
			// same types, functions, ssa values, etc., which can be very confusing
			// when debugging.
			packageIDs := map[string]bool{}
			for _, pkg := range pkgs {
				packageIDs[pkg.ID] = true
			}

			pkgs = slices.Filter(pkgs, func(pkg *packages.Package) bool {
				return !packageIDs[fmt.Sprintf("%s [%s.test]", pkg.ID, pkg.ID)]
			})
		}
		return pkgs, nil
	}
}
