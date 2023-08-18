# Unification based pointer analysis for Go

[![Go Reference](https://pkg.go.dev/badge/golang.org/x/tools/go/pointer.svg)](https://pkg.go.dev/golang.org/x/tools/go/pointer)

This repository contains a Go adaptation of [Steensgaard's pointer analysis algorithm][steensgaard].

The analysis is field-sensitive and context-insensitive.

Having field-sensitivity means that the analysis cannot run in $O(n\cdot\alpha(n))$ time (where $n$ is the size of the program), which is the runtime of the algorithm presented in the paper.
Other details, such as handling dynamic dispatch for interface methods, also prevent us from obtaining the above runtime.
It should still be fast, though.
The goal is that this implementation should be significantly faster than the implementation of [Andersen's pointer analysis algorithm][andersen] provided by [the Go team][gopointer] (with a precision trade-off).

This implementation makes many of the same design choices as the implementation of Andersen's algorithm.
Notably, arrays (and slices) are modelled as having 1 element, conversions using unsafe.Pointer are not modelled soundly, and the effects of opaque code (runtime, Cgo, etc.) is under-approximated.
The API is also similar.

Contrary to the implementation of Andersen's algorithm, no special modelling is offered for reflection (which is available under a flag there).
Also, in this implementation constraint generation is interleaved with constraint solving.
This makes it easy to only generate constraints for reachable code, which the Andersen implementation does not do.

[andersen]: https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=b7efe971a34a0f2482e0b2520ffb31062dcdde62
[gopointer]: https://pkg.go.dev/golang.org/x/tools/go/pointer
[steensgaard]: https://dl.acm.org/doi/abs/10.1145/237721.237727
