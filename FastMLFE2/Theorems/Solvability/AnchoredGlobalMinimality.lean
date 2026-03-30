import FastMLFE2.Theorems.Solvability.AnchoredClosedForm
import FastMLFE2.Theorems.Solvability.AnchoredInvertibility

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace AnchoredLocalContext

variable {ι : Type*} [Fintype ι]

private theorem normalMatrix_quadratic_form_nonneg
    (ctx : AnchoredLocalContext ι) [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight)
    (d : LocalUnknown) :
    0 ≤ (ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) * foreground d ^ 2 +
      2 * (ctx.alphaCenter * (1 - ctx.alphaCenter)) * (foreground d * background d) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) * background d ^ 2 := by
  set a := ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight with ha_def
  set b := (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight with hb_def
  set c := ctx.alphaCenter * (1 - ctx.alphaCenter) with hc_def
  set x := foreground d
  set y := background d
  have ha : 0 < a := by
    simp only [ha_def]
    linarith [AnchoredLocalContext.totalWeight_pos ctx, sq_nonneg ctx.alphaCenter]
  have hdet : 0 < a * b - c ^ 2 := by
    have := AnchoredLocalContext.closedFormDenom_pos ctx hfg hbg
    simpa [AnchoredLocalContext.closedFormDenom, ha_def, hb_def, hc_def] using this
  nlinarith [sq_nonneg (a * x + c * y), sq_nonneg y,
    show a * (a * x ^ 2 + 2 * c * (x * y) + b * y ^ 2) =
        (a * x + c * y) ^ 2 + (a * b - c ^ 2) * y ^ 2 by ring]

private theorem neighborSum_expand (ctx : AnchoredLocalContext ι) (f b : ℝ) :
    (∑ j, ctx.neighborWeight j *
        ((f - ctx.fgNeighbor j) ^ 2 + (b - ctx.bgNeighbor j) ^ 2)) =
      ctx.totalWeight * f ^ 2 - 2 * f * ctx.foregroundSum +
        (∑ j, ctx.neighborWeight j * ctx.fgNeighbor j ^ 2) +
        (ctx.totalWeight * b ^ 2 - 2 * b * ctx.backgroundSum +
        (∑ j, ctx.neighborWeight j * ctx.bgNeighbor j ^ 2)) := by
  have : ∀ j ∈ Finset.univ,
      ctx.neighborWeight j *
        ((f - ctx.fgNeighbor j) ^ 2 + (b - ctx.bgNeighbor j) ^ 2) =
      ctx.neighborWeight j * f ^ 2 - 2 * f * (ctx.neighborWeight j * ctx.fgNeighbor j) +
        ctx.neighborWeight j * ctx.fgNeighbor j ^ 2 +
        (ctx.neighborWeight j * b ^ 2 - 2 * b * (ctx.neighborWeight j * ctx.bgNeighbor j) +
        ctx.neighborWeight j * ctx.bgNeighbor j ^ 2) := fun j _ => by ring
  rw [Finset.sum_congr rfl this]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [AnchoredLocalContext.totalWeight_eq, AnchoredLocalContext.foregroundSum_eq,
    AnchoredLocalContext.backgroundSum_eq]

private theorem localCost_sub_closedForm_eq
    (ctx : AnchoredLocalContext ι) [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight)
    (g : LocalUnknown) :
    ctx.localCost g - ctx.localCost ctx.closedFormSolution =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) *
          (foreground g - foreground ctx.closedFormSolution) ^ 2 +
        2 * (ctx.alphaCenter * (1 - ctx.alphaCenter)) *
          ((foreground g - foreground ctx.closedFormSolution) *
            (background g - background ctx.closedFormSolution)) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) *
          (background g - background ctx.closedFormSolution) ^ 2 := by
  have hfgSolve :
      (ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) *
          foreground ctx.closedFormSolution +
        ctx.alphaCenter * (1 - ctx.alphaCenter) * background ctx.closedFormSolution =
      ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior := by
    have h0 := closedForm_foreground_solves ctx hfg hbg
    rw [AnchoredLocalContext.normalMatrix_mulVec_foreground,
      show ctx.rhs 0 = foreground ctx.rhs from rfl,
      AnchoredLocalContext.foreground_rhs] at h0
    linarith
  have hbgSolve :
      ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground ctx.closedFormSolution +
        ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) *
          background ctx.closedFormSolution =
      (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior := by
    have h1 := closedForm_background_solves ctx hfg hbg
    rw [AnchoredLocalContext.normalMatrix_mulVec_background,
      show ctx.rhs 1 = background ctx.rhs from rfl,
      AnchoredLocalContext.background_rhs] at h1
    linarith
  set f := foreground g
  set b := background g
  set f' := foreground ctx.closedFormSolution
  set b' := background ctx.closedFormSolution
  set α := ctx.alphaCenter
  set W := ctx.totalWeight
  set I := ctx.imageValue
  set fS := ctx.foregroundSum
  set bS := ctx.backgroundSum
  set pF := ctx.fgPrior
  set pB := ctx.bgPrior
  set lamF := ctx.fgAnchorWeight
  set lamB := ctx.bgAnchorWeight
  have hNeighborG :
      (∑ j,
          ctx.toLocalContext.neighborWeight j *
            ((foreground g - ctx.toLocalContext.fgNeighbor j) ^ 2 +
              (background g - ctx.toLocalContext.bgNeighbor j) ^ 2)) =
        ctx.totalWeight * foreground g ^ 2 - 2 * foreground g * ctx.foregroundSum +
          (∑ j, ctx.neighborWeight j * ctx.fgNeighbor j ^ 2) +
          (ctx.totalWeight * background g ^ 2 - 2 * background g * ctx.backgroundSum +
            (∑ j, ctx.neighborWeight j * ctx.bgNeighbor j ^ 2)) := by
    simpa [AnchoredLocalContext.neighborWeight, AnchoredLocalContext.toLocalContext] using
      neighborSum_expand ctx (foreground g) (background g)
  have hNeighborClosed :
      (∑ j,
          ctx.toLocalContext.neighborWeight j *
            ((foreground ctx.closedFormSolution - ctx.toLocalContext.fgNeighbor j) ^ 2 +
              (background ctx.closedFormSolution - ctx.toLocalContext.bgNeighbor j) ^ 2)) =
        ctx.totalWeight * foreground ctx.closedFormSolution ^ 2 -
            2 * foreground ctx.closedFormSolution * ctx.foregroundSum +
          (∑ j, ctx.neighborWeight j * ctx.fgNeighbor j ^ 2) +
          (ctx.totalWeight * background ctx.closedFormSolution ^ 2 -
            2 * background ctx.closedFormSolution * ctx.backgroundSum +
            (∑ j, ctx.neighborWeight j * ctx.bgNeighbor j ^ 2)) := by
    simpa [AnchoredLocalContext.neighborWeight, AnchoredLocalContext.toLocalContext] using
      neighborSum_expand ctx (foreground ctx.closedFormSolution) (background ctx.closedFormSolution)
  simp only [AnchoredLocalContext.localCost, LocalContext.localCost, LocalContext.compositingResidual_eq]
  rw [hNeighborG, hNeighborClosed]
  simp only [AnchoredLocalContext.toLocalContext_alphaCenter,
    AnchoredLocalContext.toLocalContext_imageValue] 
  linear_combination 2 * (f - f') * hfgSolve + 2 * (b - b') * hbgSolve

theorem localCost_closedFormSolution_le
    (ctx : AnchoredLocalContext ι) [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight)
    (g : LocalUnknown) :
    ctx.localCost ctx.closedFormSolution ≤ ctx.localCost g := by
  have hqf := normalMatrix_quadratic_form_nonneg ctx hfg hbg
    (mkLocalUnknown
      (foreground g - foreground ctx.closedFormSolution)
      (background g - background ctx.closedFormSolution))
  simp only [foreground_mkLocalUnknown, background_mkLocalUnknown] at hqf
  linarith [localCost_sub_closedForm_eq ctx hfg hbg g]

end AnchoredLocalContext

end FastMLFE2.Theorems
