package pointer

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"golang.org/x/tools/go/ssa"
)

var T = t

func TestTerms(t *testing.T) {
	t.Run("Closure", func(t *testing.T) {
		prog := ssa.NewProgram(nil, 0)
		fun := prog.NewFunction("synth", nil, "synth")
		ctx := &aContext{
			config:  AnalysisConfig{Program: prog},
			visited: make(map[*ssa.Function]bool),
		}

		t1 := T(tClosure{called: true, rval: mkFresh()})
		t2 := T(tClosure{funs: map[*ssa.Function][]*term{fun: nil}, rval: mkFresh()})
		ctx.unify(t1, t2)

		require.Same(t, find(t1), t2, "t1 should become a child of t2")
		require.Same(t, find(t2), t2, "t2 should be the representative")
		assert.True(t, t2.x.(tClosure).called, "'called' flag of t2 should be true")
	})
}
