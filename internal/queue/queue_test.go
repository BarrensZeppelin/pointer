package queue

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestQueue(t *testing.T) {
	var q Queue[int]
	assert.True(t, q.Empty())

	q.Push(1)
	assert.False(t, q.Empty())
	assert.Equal(t, q.Pop(), 1)
	assert.True(t, q.Empty())

	q.Push(2)
	q.Push(3)

	assert.Equal(t, q.Pop(), 2)
	assert.Equal(t, q.Pop(), 3)
	assert.True(t, q.Empty())

	assert.Panics(t, func() { q.Pop() })
}
