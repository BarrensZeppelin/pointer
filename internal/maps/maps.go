package maps

func FromKeys[L ~[]K, K comparable](l L) map[K]struct{} {
	res := make(map[K]struct{}, len(l))
	for _, key := range l {
		res[key] = struct{}{}
	}
	return res
}

func Keys[M ~map[K]V, K comparable, V any](m M) []K {
	keys := make([]K, 0, len(m))
	for key := range m {
		keys = append(keys, key)
	}
	return keys
}
