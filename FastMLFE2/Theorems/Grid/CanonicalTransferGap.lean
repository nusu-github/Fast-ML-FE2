import FastMLFE2.Theorems.Grid.CanonicalStepStability

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Canonical

namespace Canonical

theorem gridStateDistance_resizeSomeGridState_le
    (src dst : RealLevelSpec)
    (x y : GridState src.height src.width) :
    _root_.FastMLFE2.Theorems.Canonical.gridStateDistance dst
        (resizeSomeGridState dst ⟨src, x⟩)
        (resizeSomeGridState dst ⟨src, y⟩) ≤
      _root_.FastMLFE2.Theorems.Canonical.gridStateDistance src x y := by
  letI : Fact (0 < src.height) := ⟨src.heightPos⟩
  letI : Fact (0 < src.width) := ⟨src.widthPos⟩
  refine _root_.FastMLFE2.Theorems.Canonical.gridStateDistance_le_of_pointwise dst _ _ ?_
  intro p
  simpa [gridStateDistance, resizeSomeGridState] using
    localInfinityNorm_sub_le_gridStateDistance src x y
      (nearestNeighborPixel
        (hSrc := src.height) (wSrc := src.width)
        (hDst := dst.height) (wDst := dst.width) p)

@[simp] theorem gridStateDistance_resizeSomeGridState_sameSize
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width) :
    _root_.FastMLFE2.Theorems.Canonical.gridStateDistance spec
        (resizeSomeGridState spec ⟨spec, x⟩)
        (resizeSomeGridState spec ⟨spec, y⟩) =
      _root_.FastMLFE2.Theorems.Canonical.gridStateDistance spec x y := by
  simp [_root_.FastMLFE2.Theorems.Canonical.gridStateDistance, resizeSomeGridState_sameSize]

end Canonical

end FastMLFE2.Theorems
