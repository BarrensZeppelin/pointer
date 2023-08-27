package pointer

import (
	"fmt"
	"go/types"

	"golang.org/x/tools/go/types/typeutil"
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

	panic(fmt.Errorf("no field on %v named %s", t, fieldName))
}

type typemap[V any] struct{ typeutil.Map }

func (m *typemap[V]) Has(key types.Type) bool     { return m.Map.At(key) != nil }
func (m *typemap[V]) At(key types.Type) V         { return m.Map.At(key).(V) }
func (m *typemap[V]) Set(key types.Type, value V) { m.Map.Set(key, value) }

func (m *typemap[V]) Iterate(f func(key types.Type, value V)) {
	m.Map.Iterate(func(key types.Type, value any) { f(key, value.(V)) })
}
