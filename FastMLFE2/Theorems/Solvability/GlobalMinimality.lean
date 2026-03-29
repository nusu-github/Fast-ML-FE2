import FastMLFE2.Theorems.Solvability.ClosedForm
import FastMLFE2.Theorems.Solvability.Invertibility

namespace FastMLFE2.Theorems

/-!
# Global minimality of the closed-form solution

The local cost function is a convex quadratic:
  localCost g = gᵀ M g − 2 rhsᵀ g + C
where M = normalMatrix is positive definite under `CoreMathAssumptions`.
Therefore the unique stationary point `closedFormSolution` is the global minimizer.
-/

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- The 2×2 quadratic form `d^T M d` is non-negative when M = normalMatrix is
positive definite. Proof: complete the square using `det M > 0` and `diag > 0`. -/
private theorem normalMatrix_quadratic_form_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (d : LocalUnknown) :
    0 ≤ (ctx.alphaCenter ^ 2 + ctx.totalWeight) * foreground d ^ 2 +
      2 * (ctx.alphaCenter * (1 - ctx.alphaCenter)) * (foreground d * background d) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * background d ^ 2 := by
  set a := ctx.alphaCenter ^ 2 + ctx.totalWeight with ha_def
  set b := (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight with hb_def
  set c := ctx.alphaCenter * (1 - ctx.alphaCenter) with hc_def
  set x := foreground d
  set y := background d
  have ha : 0 < a := by
    simp only [ha_def]; linarith [totalWeight_pos ctx, sq_nonneg ctx.alphaCenter]
  have hdet : 0 < a * b - c ^ 2 := by
    have := normalMatrix_det_pos ctx
    rw [normalMatrix_det] at this
    simp only [LocalContext.weightedMeanDenom] at this
    nlinarith [totalWeight_pos ctx]
  nlinarith [sq_nonneg (a * x + c * y), sq_nonneg y,
    show a * (a * x ^ 2 + 2 * c * (x * y) + b * y ^ 2) =
        (a * x + c * y) ^ 2 + (a * b - c ^ 2) * y ^ 2 by ring]

/-- The neighbor contribution to localCost splits as a sum of individual terms.
Each `(f - fj)^2` expands to `f^2 - 2*f*fj + fj^2`, yielding W*f^2 - 2*fS*f + ∑wj*fj^2`. -/
private theorem neighborSum_expand (ctx : LocalContext ι) (f b : ℝ) :
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
  simp only [LocalContext.totalWeight, LocalContext.foregroundSum, LocalContext.backgroundSum]

/-- Cost difference identity:
  `localCost g − localCost g* = (g − g*)^T M (g − g*)`. -/
private theorem localCost_sub_closedForm_eq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (g : LocalUnknown) :
    ctx.localCost g - ctx.localCost (closedFormSolution ctx) =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight) *
          (foreground g - foreground (closedFormSolution ctx)) ^ 2 +
        2 * (ctx.alphaCenter * (1 - ctx.alphaCenter)) *
          ((foreground g - foreground (closedFormSolution ctx)) *
            (background g - background (closedFormSolution ctx))) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) *
          (background g - background (closedFormSolution ctx)) ^ 2 := by
  -- Extract the normal equation for the closed-form solution (before `set`)
  have hsolve := closedForm_solvesNormalEquation ctx
  have hfg : (ctx.alphaCenter ^ 2 + ctx.totalWeight) *
        foreground (closedFormSolution ctx) +
      ctx.alphaCenter * (1 - ctx.alphaCenter) * background (closedFormSolution ctx) =
      ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum := by
    have h0 := closedForm_foreground_solves ctx
    rw [normalMatrix_mulVec_foreground, show ctx.rhs 0 = foreground ctx.rhs from rfl,
      rhs_foreground] at h0
    linarith
  have hbg : ctx.alphaCenter * (1 - ctx.alphaCenter) *
        foreground (closedFormSolution ctx) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) *
        background (closedFormSolution ctx) =
      (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum := by
    have h1 := closedForm_background_solves ctx
    rw [normalMatrix_mulVec_background, show ctx.rhs 1 = background ctx.rhs from rfl,
      rhs_background] at h1
    linarith
  -- Abbreviations (after extracting normal-equation hypotheses)
  set f := foreground g
  set b := background g
  set f' := foreground (closedFormSolution ctx)
  set b' := background (closedFormSolution ctx)
  set α := ctx.alphaCenter
  set W := ctx.totalWeight
  set I := ctx.imageValue
  set fS := ctx.foregroundSum
  set bS := ctx.backgroundSum
  -- Also set the constant sum terms so they cancel
  set C_fg := ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j ^ 2
  set C_bg := ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j ^ 2
  -- Expand localCost using definitions
  simp only [LocalContext.localCost, compositingResidual_eq]
  rw [neighborSum_expand, neighborSum_expand]
  -- Now it's a pure algebraic identity given hfg, hbg
  linear_combination 2 * (f - f') * hfg + 2 * (b - b') * hbg

/-- **Global minimality**: the closed-form solution minimizes the local cost function
over all `LocalUnknown` vectors. -/
theorem localCost_closedFormSolution_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (g : LocalUnknown) :
    ctx.localCost (closedFormSolution ctx) ≤ ctx.localCost g := by
  have hqf := normalMatrix_quadratic_form_nonneg ctx
    (mkLocalUnknown
      (foreground g - foreground (closedFormSolution ctx))
      (background g - background (closedFormSolution ctx)))
  simp only [foreground_mkLocalUnknown, background_mkLocalUnknown] at hqf
  linarith [localCost_sub_closedForm_eq ctx g]

end LocalContext

end FastMLFE2.Theorems
