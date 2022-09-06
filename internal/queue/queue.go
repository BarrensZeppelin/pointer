package queue

import "errors"

type Queue[E any] struct {
	elements []E
}

func (q *Queue[E]) Push(e E) {
	q.elements = append(q.elements, e)
}

func (q *Queue[E]) Empty() bool {
	return len(q.elements) == 0
}

var ErrEmpty = errors.New("Queue is empty")

func (q *Queue[E]) Pop() E {
	if q.Empty() {
		panic(ErrEmpty)
	}

	e := q.elements[0]
	q.elements = q.elements[1:]
	return e
}
