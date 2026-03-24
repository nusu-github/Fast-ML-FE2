import FastMLFE2.Theorems.NearBinary
import FastMLFE2.Theorems.BinaryAlpha

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def meanResidualSolution (ctx : LocalContext ι) : LocalUnknown :=
  mkLocalUnknown
    (ctx.foregroundMean + ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom)
    (ctx.backgroundMean + (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom)

@[simp] theorem foreground_meanResidualSolution (ctx : LocalContext ι) :
    foreground (meanResidualSolution ctx) =
      ctx.foregroundMean + ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom := by
  simp [meanResidualSolution]

@[simp] theorem background_meanResidualSolution (ctx : LocalContext ι) :
    background (meanResidualSolution ctx) =
      ctx.backgroundMean + (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom := by
  simp [meanResidualSolution]

@[simp] theorem foreground_clamp01_meanResidualSolution (ctx : LocalContext ι) :
    foreground (clamp01 (meanResidualSolution ctx)) =
      clamp01Scalar
        (ctx.foregroundMean + ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom) := by
  simp [meanResidualSolution]

@[simp] theorem background_clamp01_meanResidualSolution (ctx : LocalContext ι) :
    background (clamp01 (meanResidualSolution ctx)) =
      clamp01Scalar
        (ctx.backgroundMean +
          (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom) := by
  simp [meanResidualSolution]

theorem meanResidualSolution_eq_closedFormSolution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    meanResidualSolution ctx = closedFormSolution ctx := by
  funext i
  fin_cases i
  · simpa [foreground, meanResidualSolution, mkLocalUnknown] using
      (foreground_correction_uses_meanResidual (ctx := ctx)).symm
  · simpa [background, meanResidualSolution, mkLocalUnknown] using
      (background_correction_uses_meanResidual (ctx := ctx)).symm

theorem clamp01_meanResidualSolution_eq_clamp01_closedFormSolution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    clamp01 (meanResidualSolution ctx) = clamp01 (closedFormSolution ctx) := by
  simp [meanResidualSolution_eq_closedFormSolution (ctx := ctx)]

theorem meanResidualSolution_foreground_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 0) :
    foreground (meanResidualSolution ctx) = ctx.foregroundMean := by
  rw [meanResidualSolution_eq_closedFormSolution ctx]
  rw [closedFormSolution_eq_of_alpha_zero ctx hα]
  simp only [foregroundSum_eq_sum_neighborWeight_mul, totalWeight_eq_sum_neighborWeight,
    backgroundSum_eq_sum_neighborWeight_mul, foreground_mkLocalUnknown, foregroundMean]

theorem meanResidualSolution_background_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 0) :
    background (meanResidualSolution ctx) =
      ctx.backgroundMean +
        (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1) := by
  rw [meanResidualSolution_eq_closedFormSolution ctx]
  rw [closedFormSolution_eq_of_alpha_zero ctx hα]
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have htw1 : ctx.totalWeight + 1 ≠ 0 := by linarith [totalWeight_pos ctx]
  simp only [foregroundSum_eq_sum_neighborWeight_mul, totalWeight_eq_sum_neighborWeight,
    backgroundSum_eq_sum_neighborWeight_mul, background_mkLocalUnknown, backgroundMean]
  set W := ∑ j, ctx.neighborWeight j
  set BG := ∑ x, ctx.neighborWeight x * ctx.bgNeighbor x
  have hW1 : W + 1 ≠ 0 := htw1
  have hW0 : W ≠ 0 := htw0
  have hW1' : 1 + W ≠ 0 := by rw [add_comm]; exact hW1
  field_simp [hW0, hW1, hW1']
  ring

theorem meanResidualSolution_foreground_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 1) :
    foreground (meanResidualSolution ctx) =
      ctx.foregroundMean +
        (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1) := by
  rw [meanResidualSolution_eq_closedFormSolution ctx]
  rw [closedFormSolution_eq_of_alpha_one ctx hα]
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have htw1 : ctx.totalWeight + 1 ≠ 0 := by linarith [totalWeight_pos ctx]
  simp only [foregroundSum_eq_sum_neighborWeight_mul, totalWeight_eq_sum_neighborWeight,
    backgroundSum_eq_sum_neighborWeight_mul, foreground_mkLocalUnknown, foregroundMean]
  set W := ∑ j, ctx.neighborWeight j
  set FG := ∑ x, ctx.neighborWeight x * ctx.fgNeighbor x
  have hW1 : W + 1 ≠ 0 := htw1
  have hW0 : W ≠ 0 := htw0
  have hW1' : 1 + W ≠ 0 := by rw [add_comm]; exact hW1
  field_simp [hW0, hW1, hW1']
  ring

theorem meanResidualSolution_background_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 1) :
    background (meanResidualSolution ctx) = ctx.backgroundMean := by
  rw [meanResidualSolution_eq_closedFormSolution ctx]
  rw [closedFormSolution_eq_of_alpha_one ctx hα]
  simp only [foregroundSum_eq_sum_neighborWeight_mul, totalWeight_eq_sum_neighborWeight,
    backgroundSum_eq_sum_neighborWeight_mul, background_mkLocalUnknown, backgroundMean]

end LocalContext

end FastMLFE2.Theorems
