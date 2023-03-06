package pointer

import (
	"fmt"
	"go/types"
	"log"

	"golang.org/x/tools/go/ssa"
)

// This file contains definitions of types whose instances represent abstract
// objects that are targets of pointers in the analysed program.

// Label denotes an abstract object.
// A label is either an [AllocationSite], representing the object allocated at
// a given instruction, or a [FieldPointer] & [ElementPointer], representing a
// subobject of another object (field of a struct or element of slice/array,
// respectively).
type Label interface {
	// Allocation site of the object denoted by the label.
	Site() ssa.Value
	// Returns an access path to the object that is compatible with the paths
	// provided for labels in the Go team implementation of Andersen's pointer
	// analysis. Specifically field names are resolved from ssa indices.
	Path() string
	// Returns the type of a pointer pointing to the object denoted by the
	// label. (Label).Type().Underlying() == (*types.Pointer) except for
	// allocation sites for slices (where the returned type is (*types.Slice)).
	Type() types.Type
}

type AllocationSite struct{ site ssa.Value }

func (a AllocationSite) Site() ssa.Value  { return a.site }
func (a AllocationSite) Path() string     { return "" }
func (a AllocationSite) Type() types.Type { return a.site.Type() }

type FieldPointer struct {
	base  Label
	Field int
}

func (fp FieldPointer) Site() ssa.Value { return fp.base.Site() }
func (fp FieldPointer) Path() string {
	bt := fp.base.Type().Underlying().(*types.Pointer).Elem().Underlying().(*types.Struct)
	return fmt.Sprintf("%s.%s", fp.base.Path(), bt.Field(fp.Field).Name())
}
func (fp FieldPointer) Type() types.Type {
	bt := fp.base.Type().Underlying().(*types.Pointer).Elem().Underlying().(*types.Struct)
	return types.NewPointer(bt.Field(fp.Field).Type())
}

type ElementPointer struct{ base Label }

func (ep ElementPointer) Site() ssa.Value { return ep.base.Site() }
func (ep ElementPointer) Path() string    { return ep.base.Path() + "[*]" }
func (ep ElementPointer) Type() types.Type {
	switch bt := ep.base.Type().Underlying().(type) {
	case *types.Pointer:
		return types.NewPointer(bt.Elem().Underlying().(*types.Array).Elem())
	case *types.Slice:
		return types.NewPointer(bt.Elem())
	default:
		log.Fatalf("Underlying type of ElementPointer should be slice or pointer, was: %T", bt)
		return nil
	}
}
