package pkgutil

import (
	"errors"
	"os"

	"golang.org/x/tools/go/packages"
)

func LoadPackagesFromSource(source string) ([]*packages.Package, error) {
	// We use the Overlay mechanism to allow the tool to load a non-existent file.
	config := &packages.Config{
		Mode:  packages.LoadAllSyntax,
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
		return pkgs, nil
	}
}
