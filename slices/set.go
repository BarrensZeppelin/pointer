package slices

func Contains[L ~[]E, E comparable](l L, x E) bool {
	for _, y := range l {
		if x == y {
			return true
		}
	}

	return false
}

func Subset[L ~[]E, E comparable](a, b L) bool {
	if len(a) > len(b) {
		return false
	}

	for _, x := range a {
		if !Contains(b, x) {
			return false
		}
	}

	return true
}
