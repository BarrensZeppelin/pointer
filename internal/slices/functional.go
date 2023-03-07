package slices

func Map[L ~[]X, X, Y any](l L, f func(X) Y) []Y {
	r := make([]Y, len(l))
	for i, x := range l {
		r[i] = f(x)
	}
	return r
}
