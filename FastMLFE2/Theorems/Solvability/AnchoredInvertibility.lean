import FastMLFE2.Core.AnchoredClosedForm
import FastMLFE2.Theorems.Solvability.Invertibility

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace AnchoredLocalContext

variable {ι : Type*} [Fintype ι]

theorem totalWeight_pos (ctx : AnchoredLocalContext ι) [CoreMathAssumptions ctx.toLocalContext] :
    0 < ctx.totalWeight :=
  FastMLFE2.Theorems.LocalContext.totalWeight_pos ctx.toLocalContext

theorem closedFormDenom_eq_det (ctx : AnchoredLocalContext ι) :
    ctx.closedFormDenom = ctx.normalMatrix.det := by
  rw [AnchoredLocalContext.closedFormDenom, Matrix.det_fin_two]
  simp [AnchoredLocalContext.normalMatrix]
  ring

theorem closedFormDenom_pos (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight) :
    0 < ctx.closedFormDenom := by
  have hbase : 0 < ctx.toLocalContext.normalMatrix.det :=
    FastMLFE2.Theorems.LocalContext.normalMatrix_det_pos ctx.toLocalContext
  have h00 : 0 < ctx.alphaCenter ^ 2 + ctx.totalWeight := by
    linarith [totalWeight_pos ctx, sq_nonneg ctx.alphaCenter]
  have h11 : 0 < (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight := by
    linarith [totalWeight_pos ctx, sq_nonneg (1 - ctx.alphaCenter)]
  have hdet :
      ctx.toLocalContext.normalMatrix.det =
        (ctx.alphaCenter ^ 2 + ctx.totalWeight) * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) -
          (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 := by
    rw [FastMLFE2.Theorems.LocalContext.normalMatrix_det]
    simp [AnchoredLocalContext.totalWeight, LocalContext.weightedMeanDenom]
    ring
  have hsplit :
      ctx.closedFormDenom =
        ctx.toLocalContext.normalMatrix.det +
          ctx.fgAnchorWeight * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) +
          ctx.bgAnchorWeight * (ctx.alphaCenter ^ 2 + ctx.totalWeight) +
          ctx.fgAnchorWeight * ctx.bgAnchorWeight := by
    rw [AnchoredLocalContext.closedFormDenom, hdet]
    ring_nf
  have hrest :
      0 ≤
        ctx.fgAnchorWeight * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) +
          ctx.bgAnchorWeight * (ctx.alphaCenter ^ 2 + ctx.totalWeight) +
          ctx.fgAnchorWeight * ctx.bgAnchorWeight := by
    nlinarith
  rw [hsplit]
  nlinarith

theorem closedFormDenom_ne_zero (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight) :
    ctx.closedFormDenom ≠ 0 :=
  (closedFormDenom_pos ctx hfg hbg).ne'

end AnchoredLocalContext

end FastMLFE2.Theorems
