import FastMLFE2.FixedPrecision.Cost
import FastMLFE2.FixedPrecision.Multilevel
import FastMLFE2.Canonical.MultilevelSchedule

namespace FastMLFE2.Theorems

open FastMLFE2.FixedPrecision
open FastMLFE2.Canonical

namespace FixedPrecision

theorem fullyFixedNearestNeighborResize_sameSize
    {cfg : FixedFormat} {h w : Nat}
    [Fact (0 < h)] [Fact (0 < w)]
    (state : FixedGridState cfg h w) :
    fullyFixedNearestNeighborResize (hSrc := h) (wSrc := w) (hDst := h) (wDst := w) state = state := by
  exact FastMLFE2.FixedPrecision.fullyFixedNearestNeighborResize_self
    (cfg := cfg) (h := h) (w := w) state

theorem redBlackSweep_eq_self_of_jacobiFixed
    {cfg : FixedFormat} {h w : Nat}
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w)
    (hFix : builder.fullyFixedJacobiStep state = state) :
    builder.fullyFixedRedBlackSweep state = state := by
  simpa using FixedGridBuilder.fullyFixedRedBlackSweep_eq_self_of_jacobiFixed builder state hFix

theorem jacobiStep_eq_self_of_redBlackSweepFixed
    {cfg : FixedFormat} {h w : Nat}
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w)
    (hFix : builder.fullyFixedRedBlackSweep state = state) :
    builder.fullyFixedJacobiStep state = state := by
  simpa using FixedGridBuilder.fullyFixedJacobi_eq_self_of_redBlackSweep_fixed builder state hFix

theorem multilevelCost_nonneg'
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg)
    (levels : List FixedLevelSpec) :
    0 ≤ multilevelCost model family seed levels := by
  exact FastMLFE2.FixedPrecision.multilevelCost_nonneg model family seed levels

theorem fullyFixedMultilevelRun_nil
    {cfg : FixedFormat}
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg) :
    fullyFixedMultilevelRun family seed [] = seed := by
  simp [fullyFixedMultilevelRun]

end FixedPrecision

end FastMLFE2.Theorems
