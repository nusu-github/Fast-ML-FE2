import FastMLFE2.Theorems.ClosedForm
import FastMLFE2.Theorems.ClosedFormBoxInput
import FastMLFE2.Theorems.Invertibility
import FastMLFE2.Theorems.Conditioning

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def binaryZeroCtx (ctx : LocalContext ι) : LocalContext ι := ctx.withAlphaCenter 0

def weightDriftBudget (ctx : LocalContext ι) (a : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) * ctx.omega * a

omit [Fintype ι] in
theorem neighborWeight_sub_binaryZero_le
    (ctx : LocalContext ι) (a : ℝ) (j : ι) (hω : 0 ≤ ctx.omega) :
    |(ctx.withAlphaCenter a).neighborWeight j - (binaryZeroCtx ctx).neighborWeight j| ≤
      ctx.omega * |a| := by
  have hEq : (ctx.withAlphaCenter a).neighborWeight j - (binaryZeroCtx ctx).neighborWeight j =
      ctx.omega * (|a - ctx.alphaNeighbor j| - |0 - ctx.alphaNeighbor j|) := by
    simp [LocalContext.neighborWeight, LocalContext.withAlphaCenter, binaryZeroCtx]; ring_nf
  rw [hEq, abs_mul, abs_of_nonneg hω]
  exact mul_le_mul_of_nonneg_left
    (by simpa using abs_abs_sub_abs_le_abs_sub (a - ctx.alphaNeighbor j) (0 - ctx.alphaNeighbor j))
    hω

theorem totalWeight_sub_binaryZero_le
    (ctx : LocalContext ι) (a : ℝ) (hω : 0 ≤ ctx.omega) :
    |(ctx.withAlphaCenter a).totalWeight - (binaryZeroCtx ctx).totalWeight| ≤
      weightDriftBudget ctx |a| := by
  calc |(ctx.withAlphaCenter a).totalWeight - (binaryZeroCtx ctx).totalWeight|
      = |∑ j, ((ctx.withAlphaCenter a).neighborWeight j -
          (binaryZeroCtx ctx).neighborWeight j)| := by simp [LocalContext.totalWeight]
    _ ≤ ∑ j, ctx.omega * |a| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => neighborWeight_sub_binaryZero_le ctx a j hω)
    _ = weightDriftBudget ctx |a| := by simp [weightDriftBudget]; ring

theorem foregroundSum_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1) :
    0 ≤ ctx.foregroundSum ∧ ctx.foregroundSum ≤ ctx.totalWeight :=
  ⟨Finset.sum_nonneg fun j _ => mul_nonneg (neighborWeight_nonneg ctx j) (hfg j).1,
   Finset.sum_le_sum fun j _ => by nlinarith [neighborWeight_nonneg ctx j, (hfg j).2]⟩

theorem backgroundSum_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    0 ≤ ctx.backgroundSum ∧ ctx.backgroundSum ≤ ctx.totalWeight :=
  ⟨Finset.sum_nonneg fun j _ => mul_nonneg (neighborWeight_nonneg ctx j) (hbg j).1,
   Finset.sum_le_sum fun j _ => by nlinarith [neighborWeight_nonneg ctx j, (hbg j).2]⟩

theorem foregroundMean_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1) :
    0 ≤ ctx.foregroundMean ∧ ctx.foregroundMean ≤ 1 := by
  rcases foregroundSum_mem_Icc_of_boxedNeighbors ctx hfg with ⟨hs0, hs1⟩
  have htw := totalWeight_pos ctx
  exact ⟨div_nonneg hs0 htw.le,
    (div_le_one htw).2 (by rwa [LocalContext.totalWeight_eq_sum_neighborWeight] at hs1)⟩

theorem backgroundMean_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    0 ≤ ctx.backgroundMean ∧ ctx.backgroundMean ≤ 1 := by
  rcases backgroundSum_mem_Icc_of_boxedNeighbors ctx hbg with ⟨hs0, hs1⟩
  have htw := totalWeight_pos ctx
  exact ⟨div_nonneg hs0 htw.le,
    (div_le_one htw).2 (by rwa [LocalContext.totalWeight_eq_sum_neighborWeight] at hs1)⟩

theorem foreground_closedFormSolution_sub_foregroundMean_eq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) - ctx.foregroundMean =
      ctx.alphaCenter *
        (ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
          ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean) /
        ctx.weightedMeanDenom := by
  rw [foreground_closedFormSolution_eq_weightedMeanForm]
  have hden : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'; field_simp [hden]
  simp [closedFormForegroundMeanAffine, LocalContext.weightedMeanDenom]; ring

theorem foreground_closedFormSolution_sub_foregroundMean_eq_meanResidualForm
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) - ctx.foregroundMean =
      ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom := by
  rw [foreground_closedFormSolution_sub_foregroundMean_eq]
  simp [FastMLFE2.Core.LocalContext.meanResidual]; ring

theorem foreground_correction_uses_meanResidual
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) =
      ctx.foregroundMean +
        ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom := by
  linarith [foreground_closedFormSolution_sub_foregroundMean_eq_meanResidualForm ctx]

theorem background_closedFormSolution_sub_backgroundMean_eq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) - ctx.backgroundMean =
      (1 - ctx.alphaCenter) *
        (ctx.imageValue - ctx.alphaCenter * ctx.foregroundMean -
          (1 - ctx.alphaCenter) * ctx.backgroundMean) /
        ctx.weightedMeanDenom := by
  rw [background_closedFormSolution_eq_weightedMeanForm]
  have hden : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'; field_simp [hden]
  simp [closedFormBackgroundMeanAffine, LocalContext.weightedMeanDenom]; ring

theorem background_closedFormSolution_sub_backgroundMean_eq_meanResidualForm
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) - ctx.backgroundMean =
      (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom := by
  rw [background_closedFormSolution_sub_backgroundMean_eq]
  simp [FastMLFE2.Core.LocalContext.meanResidual]

theorem background_correction_uses_meanResidual
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) =
      ctx.backgroundMean +
        (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom := by
  linarith [background_closedFormSolution_sub_backgroundMean_eq_meanResidualForm ctx]

theorem meanResidual_corrections_of_solvesNormalEquation
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    {g : LocalUnknown} (hg : ctx.SolvesNormalEquation g) :
    foreground g =
        ctx.foregroundMean +
          ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom ∧
      background g =
        ctx.backgroundMean +
          (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom := by
  rw [eq_closedFormSolution_of_solvesNormalEquation ctx hg]
  exact ⟨foreground_correction_uses_meanResidual ctx, background_correction_uses_meanResidual ctx⟩

theorem abs_foreground_closedFormSolution_sub_foregroundMean_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |foreground (closedFormSolution ctx) - ctx.foregroundMean| ≤ 2 * ctx.alphaCenter := by
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  have hμF := foregroundMean_mem_Icc_of_boxedNeighbors ctx hfg
  have hμB := backgroundMean_mem_Icc_of_boxedNeighbors ctx hbg
  rw [foreground_closedFormSolution_sub_foregroundMean_eq]
  have hinner : |ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
      ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean| ≤ 1 :=
    abs_le.2 ⟨by nlinarith [hI.1, hα.1, hα.2, hμF.1, hμF.2, hμB.1, hμB.2],
              by nlinarith [hI.2, hα.1, hα.2, hμF.1, hμF.2, hμB.1, hμB.2]⟩
  have hhalf : (1 : ℝ) / 2 ≤ ctx.weightedMeanDenom := by
    have htw : 0 ≤ ctx.totalWeight := le_of_lt (totalWeight_pos ctx)
    have hsq : (1 : ℝ) / 2 ≤ ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 :=
      one_half_le_alphaQuadratic ctx
    have hdef : ctx.weightedMeanDenom =
        ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) := by
      simp [LocalContext.weightedMeanDenom, add_assoc]
    nlinarith
  have hquot : |ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
      ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean| /
      ctx.weightedMeanDenom ≤ 2 := by
    rw [div_le_iff₀ (weightedMeanDenom_pos ctx)]
    nlinarith [hinner, hhalf]
  rw [abs_div, abs_mul, abs_of_nonneg hα.1, abs_of_pos (weightedMeanDenom_pos ctx)]
  calc ctx.alphaCenter * |_| / ctx.weightedMeanDenom
      = ctx.alphaCenter * (|_| / ctx.weightedMeanDenom) := by ring
    _ ≤ ctx.alphaCenter * 2 := mul_le_mul_of_nonneg_left hquot hα.1
    _ = 2 * ctx.alphaCenter := by ring

end LocalContext

end FastMLFE2.Theorems
