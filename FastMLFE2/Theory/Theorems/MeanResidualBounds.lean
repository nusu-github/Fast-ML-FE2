import FastMLFE2.Theory.Theorems.Invertibility

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Core.LocalContext
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem foregroundMean_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j) :
    0 ≤ ctx.foregroundMean := by
  rw [foregroundMean, foregroundSum]
  have htw := totalWeight_pos ctx
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (neighborWeight_nonneg ctx j) (hfg j)
  · exact htw.le

theorem foregroundMean_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : ∀ j, ctx.fgNeighbor j ≤ 1) :
    ctx.foregroundMean ≤ 1 := by
  rw [foregroundMean, foregroundSum]
  have htw := totalWeight_pos ctx
  rw [div_le_one htw]
  rw [totalWeight]
  apply Finset.sum_le_sum
  intro j _
  simpa using mul_le_mul_of_nonneg_left (hfg j) (neighborWeight_nonneg ctx j)

theorem backgroundMean_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j) :
    0 ≤ ctx.backgroundMean := by
  rw [backgroundMean, backgroundSum]
  have htw := totalWeight_pos ctx
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (neighborWeight_nonneg ctx j) (hbg j)
  · exact htw.le

theorem backgroundMean_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hbg : ∀ j, ctx.bgNeighbor j ≤ 1) :
    ctx.backgroundMean ≤ 1 := by
  rw [backgroundMean, backgroundSum]
  have htw := totalWeight_pos ctx
  rw [div_le_one htw]
  rw [totalWeight]
  apply Finset.sum_le_sum
  intro j _
  simpa using mul_le_mul_of_nonneg_left (hbg j) (neighborWeight_nonneg ctx j)

/-- H9: If all inputs are in [0, 1], then |meanResidual| ≤ 1. -/
theorem abs_meanResidual_le_one_of_boxed_inputs
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |meanResidual ctx| ≤ 1 := by
  rw [meanResidual]
  have hfm0 := foregroundMean_nonneg ctx (fun j => (hfg j).1)
  have hfm1 := foregroundMean_le_one ctx (fun j => (hfg j).2)
  have hbm0 := backgroundMean_nonneg ctx (fun j => (hbg j).1)
  have hbm1 := backgroundMean_le_one ctx (fun j => (hbg j).2)
  rw [abs_le]
  constructor
  · -- -1 ≤ imageValue - α * foregroundMean - (1 - α) * backgroundMean
    have : ctx.alphaCenter * ctx.foregroundMean + (1 - ctx.alphaCenter) * ctx.backgroundMean ≤ 1 := by
      calc ctx.alphaCenter * ctx.foregroundMean + (1 - ctx.alphaCenter) * ctx.backgroundMean
        _ ≤ ctx.alphaCenter * 1 + (1 - ctx.alphaCenter) * 1 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hfm1 hα.1
            · exact mul_le_mul_of_nonneg_left hbm1 (by linarith)
        _ = 1 := by ring
    linarith [hI.1]
  · -- imageValue - α * foregroundMean - (1 - α) * backgroundMean ≤ 1
    have : 0 ≤ ctx.alphaCenter * ctx.foregroundMean + (1 - ctx.alphaCenter) * ctx.backgroundMean := by
      apply add_nonneg
      · exact mul_nonneg hα.1 hfm0
      · exact mul_nonneg (by linarith) hbm0
    linarith [hI.2]

theorem alpha_sq_add_one_minus_alpha_sq_ge_half (α : ℝ) :
    1/2 ≤ α^2 + (1-α)^2 := by
  have : α^2 + (1-α)^2 = 2 * (α - 1/2)^2 + 1/2 := by ring
  rw [this]
  nlinarith

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
    rw [weightedMeanDenom]
    have htw := (totalWeight_pos ctx).le
    have hsq := alpha_sq_add_one_minus_alpha_sq_ge_half ctx.alphaCenter
    linarith
  calc ctx.alphaCenter * |meanResidual ctx| / ctx.weightedMeanDenom
    _ ≤ ctx.alphaCenter * 1 / ctx.weightedMeanDenom := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hr hα.1
        · exact hden.le
    _ ≤ ctx.alphaCenter / (1/2) := by
        rw [mul_one]
        apply div_le_div_of_nonneg_left
        · exact hα.1
        · norm_num
        · exact hD
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
    rw [weightedMeanDenom]
    have htw := (totalWeight_pos ctx).le
    have hsq := alpha_sq_add_one_minus_alpha_sq_ge_half ctx.alphaCenter
    linarith
  calc (1 - ctx.alphaCenter) * |meanResidual ctx| / ctx.weightedMeanDenom
    _ ≤ (1 - ctx.alphaCenter) * 1 / ctx.weightedMeanDenom := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hr hβ
        · exact hden.le
    _ ≤ (1 - ctx.alphaCenter) / (1/2) := by
        rw [mul_one]
        apply div_le_div_of_nonneg_left
        · exact hβ
        · norm_num
        · exact hD
    _ = 2 * (1 - ctx.alphaCenter) := by linarith

end LocalContext

end FastMLFE2.Theory.Theorems
