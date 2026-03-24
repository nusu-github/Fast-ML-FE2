import FastMLFE2.Theorems.Invertibility

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Core.LocalContext
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem foregroundMean_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j) :
    0 ≤ ctx.foregroundMean :=
  div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (neighborWeight_nonneg ctx j) (hfg j))
    (totalWeight_pos ctx).le

theorem foregroundMean_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : ∀ j, ctx.fgNeighbor j ≤ 1) :
    ctx.foregroundMean ≤ 1 := by
  rw [foregroundMean, foregroundSum, div_le_one (totalWeight_pos ctx), totalWeight]
  exact Finset.sum_le_sum fun j _ =>
    by simpa using mul_le_mul_of_nonneg_left (hfg j) (neighborWeight_nonneg ctx j)

theorem backgroundMean_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j) :
    0 ≤ ctx.backgroundMean :=
  div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (neighborWeight_nonneg ctx j) (hbg j))
    (totalWeight_pos ctx).le

theorem backgroundMean_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hbg : ∀ j, ctx.bgNeighbor j ≤ 1) :
    ctx.backgroundMean ≤ 1 := by
  rw [backgroundMean, backgroundSum, div_le_one (totalWeight_pos ctx), totalWeight]
  exact Finset.sum_le_sum fun j _ =>
    by simpa using mul_le_mul_of_nonneg_left (hbg j) (neighborWeight_nonneg ctx j)

/-- H9: If all inputs are in [0, 1], then |meanResidual| ≤ 1. -/
theorem abs_meanResidual_le_one_of_boxed_inputs
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |meanResidual ctx| ≤ 1 := by
  rw [meanResidual, abs_le]
  have hfm0 := foregroundMean_nonneg ctx (fun j => (hfg j).1)
  have hfm1 := foregroundMean_le_one ctx (fun j => (hfg j).2)
  have hbm0 := backgroundMean_nonneg ctx (fun j => (hbg j).1)
  have hbm1 := backgroundMean_le_one ctx (fun j => (hbg j).2)
  constructor <;> nlinarith [hI.1, hI.2, hα.1, hα.2]

theorem alpha_sq_add_one_minus_alpha_sq_ge_half (α : ℝ) :
    1/2 ≤ α^2 + (1-α)^2 := by nlinarith [sq_nonneg (α - 1/2)]

/-- H10 (foreground): Correction upper bound. -/
theorem abs_foreground_correction_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |ctx.alphaCenter * meanResidual ctx / ctx.weightedMeanDenom| ≤
      2 * ctx.alphaCenter := by
  have hden := weightedMeanDenom_pos ctx
  rw [abs_div, abs_mul, abs_of_nonneg hα.1, abs_of_pos hden]
  have hr := abs_meanResidual_le_one_of_boxed_inputs ctx hI hα hfg hbg
  have hD : 1/2 ≤ ctx.weightedMeanDenom := by
    rw [weightedMeanDenom]; linarith [totalWeight_pos ctx,
      alpha_sq_add_one_minus_alpha_sq_ge_half ctx.alphaCenter]
  calc ctx.alphaCenter * |meanResidual ctx| / ctx.weightedMeanDenom
      ≤ ctx.alphaCenter * 1 / ctx.weightedMeanDenom :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hα.1) hden.le
    _ ≤ ctx.alphaCenter / (1/2) := by
        rw [mul_one]; exact div_le_div_of_nonneg_left hα.1 (by norm_num) hD
    _ = 2 * ctx.alphaCenter := by linarith

/-- H10 (background): Correction upper bound. -/
theorem abs_background_correction_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |(1 - ctx.alphaCenter) * meanResidual ctx / ctx.weightedMeanDenom| ≤
      2 * (1 - ctx.alphaCenter) := by
  have hden := weightedMeanDenom_pos ctx
  have hβ : 0 ≤ 1 - ctx.alphaCenter := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hβ, abs_of_pos hden]
  have hr := abs_meanResidual_le_one_of_boxed_inputs ctx hI hα hfg hbg
  have hD : 1/2 ≤ ctx.weightedMeanDenom := by
    rw [weightedMeanDenom]; linarith [totalWeight_pos ctx,
      alpha_sq_add_one_minus_alpha_sq_ge_half ctx.alphaCenter]
  calc (1 - ctx.alphaCenter) * |meanResidual ctx| / ctx.weightedMeanDenom
      ≤ (1 - ctx.alphaCenter) * 1 / ctx.weightedMeanDenom :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hβ) hden.le
    _ ≤ (1 - ctx.alphaCenter) / (1/2) := by
        rw [mul_one]; exact div_le_div_of_nonneg_left hβ (by norm_num) hD
    _ = 2 * (1 - ctx.alphaCenter) := by linarith

end LocalContext

end FastMLFE2.Theorems
