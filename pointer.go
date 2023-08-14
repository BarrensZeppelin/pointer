package pointer

import "golang.org/x/tools/go/ssa"

// Interface for structures collected during analysis required to build the
// points-to relation after analysis finishes.
type prePTag interface {
	prePTag()
}
type pptag struct{}

func (pptag) prePTag() {}

// prePSite denotes the object allocated at the given allocation site.
type prePSite struct {
	pptag
	site ssa.Value
}

// prePSynth denotes a synthetically allocated object.
type prePSynth struct {
	pptag
	label string
}

// prePSite denotes the object accessed from the i'th field on the given base.
// -1 indicates array access.
type prePAccess struct {
	pptag
	base  *Term
	field int
}
