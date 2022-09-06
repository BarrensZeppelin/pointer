package pointer

import (
	"fmt"
	"go/types"
)

func PointerLike(t types.Type) bool {
	switch t := t.(type) {
	case *types.Pointer,
		*types.Map,
		*types.Chan,
		*types.Slice,
		*types.Interface,
		*types.Signature:
		return true
	case *types.Named:
		return PointerLike(t.Underlying())
	default:
		return false
	}
}

func FieldIndex(t *types.Struct, fieldName string) int {
	for i := 0; i < t.NumFields(); i++ {
		if t.Field(i).Name() == fieldName {
			return i
		}
	}

	panic(fmt.Errorf("No field on %v named %s", t, fieldName))
}
