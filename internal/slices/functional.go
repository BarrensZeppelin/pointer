package slices

func Map[L ~[]X, X, Y any](l L, f func(X) Y) []Y {
	r := make([]Y, len(l))
	for i, x := range l {
		r[i] = f(x)
	}
	return r
}

func Filter[L ~[]X, X any](l L, f func(X) bool) (r L) {
	for _, x := range l {
		if f(x) {
			r = append(r, x)
		}
	}
	return
}
