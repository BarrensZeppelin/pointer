package pointer

import (
	"fmt"
	"reflect"

	"github.com/BarrensZeppelin/pmmap"
	"golang.org/x/tools/go/ssa"
)

type Site struct {
	ttag
	ssa.Value
	Register bool
}

func (s Site) String() string {
	if s.Register {
		return s.Name()
	}
	return fmt.Sprintf("%s = %v", s.Name(), s.Value.String())
}

func boolHash(x bool) uint64 {
	if x { return 0xDEADBEEF }
	return 0x13371337
}

type pointerHasher struct{}

func (pointerHasher) Hash(x Site) uint64 {
	return uint64(reflect.ValueOf(x.Value).Pointer()) ^ boolHash(x.Register)
}

func (pointerHasher) Equal(a, b Site) bool {
	return a == b
}

var PointerHasher pmmap.Hasher[Site] = pointerHasher{}
