import FastMLFE2.FixedPrecision.Jacobi
import FastMLFE2.Theorems.FixedPrecision.FixedPrecisionLocal
import FastMLFE2.Theorems.FixedPrecision.QuantizationBounds

namespace FastMLFE2.Theorems

open FastMLFE2.FixedPrecision

namespace FixedPrecision

open FixedLocalContext
open FixedLocalContextBuilder

variable {cfg : FixedFormat} {ι κ : Type*} [Fintype ι]
variable {η : κ → Type*} [∀ p, Fintype (η p)]

theorem fixedMeanResidualStep_eq_quantizedMeanResidualStep_of_rangeCert
    (ctx : FixedLocalContext cfg ι) (hcfg : 0 < cfg.accWidth)
    (h : LocalRangeCert ctx) :
    decodeUnknown cfg (ctx.fixedMeanResidualStep) =
      decodeUnknown cfg (ctx.quantizedMeanResidualStep) :=
  decodedStep_eq_quantizedRealStep_of_noWrap ctx (NoWrapLocalStep_of_rangeCert ctx hcfg h)

theorem decodedFixedJacobiUpdateAt_eq_of_rangeCert
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) (p : κ)
    (hcfg : 0 < cfg.accWidth) (h : LocalRangeCert (builder.build p state)) :
    decodeUnknown cfg (builder.fixedJacobiUpdateAt state p) =
      decodeUnknown cfg (FixedLocalContext.quantizedMeanResidualStep (builder.build p state)) := by
  simpa [FixedLocalContextBuilder.fixedJacobiUpdateAt] using
    fixedMeanResidualStep_eq_quantizedMeanResidualStep_of_rangeCert (builder.build p state) hcfg h

theorem decodedFixedJacobiStep_apply_eq_of_rangeCert
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) (p : κ)
    (hcfg : 0 < cfg.accWidth) (h : LocalRangeCert (builder.build p state)) :
    decodeUnknown cfg (builder.fixedJacobiStep state p) =
      decodeUnknown cfg (FixedLocalContext.quantizedMeanResidualStep (builder.build p state)) := by
  simpa [FixedLocalContextBuilder.fixedJacobiStep] using
    decodedFixedJacobiUpdateAt_eq_of_rangeCert builder state p hcfg h

theorem fixedJacobiIterate_error_le_geom_sum
    {α : Type*} [PseudoMetricSpace α]
    (T P : α → α) {ρ ε : ℝ}
    (hρ : 0 ≤ ρ)
    (hT : ∀ x y, dist (T x) (T y) ≤ ρ * dist x y)
    (hP : ∀ x, dist (P x) (T x) ≤ ε) :
    ∀ n x, dist (Nat.iterate P n x) (Nat.iterate T n x) ≤
      ε * Quantization.geomSeries ρ n :=
  Quantization.iteratePerturbation_error_le_geom_sum T P hρ hT hP

theorem fixedJacobiIterate_error_le_inv_one_sub
    {α : Type*} [PseudoMetricSpace α]
    (T P : α → α) {ρ ε : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hT : ∀ x y, dist (T x) (T y) ≤ ρ * dist x y)
    (hP : ∀ x, dist (P x) (T x) ≤ ε) (hε : 0 ≤ ε) :
    ∀ n x, dist (Nat.iterate P n x) (Nat.iterate T n x) ≤
      ε / (1 - ρ) :=
  Quantization.iteratePerturbation_error_le_inv_one_sub T P hρ hρ1 hT hP hε

end FixedPrecision

end FastMLFE2.Theorems
