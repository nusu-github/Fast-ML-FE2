import FastMLFE2.Theory.Theorems.ClosedForm
import FastMLFE2.Theory.Theorems.ClosedFormBoxInput
import FastMLFE2.Theory.Theorems.Invertibility
import FastMLFE2.Theory.Theorems.Conditioning

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def binaryZeroCtx (ctx : LocalContext ι) : LocalContext ι := ctx.withAlphaCenter 0

def weightDriftBudget (ctx : LocalContext ι) (a : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) * ctx.omega * a

omit [Fintype ι] in
theorem neighborWeight_sub_binaryZero_le
    (ctx : LocalContext ι)
    (a : ℝ)
    (j : ι)
    (hω : 0 ≤ ctx.omega) :
    |(ctx.withAlphaCenter a).neighborWeight j - (binaryZeroCtx ctx).neighborWeight j| ≤
      ctx.omega * |a| := by
  have habs :
      |(|a - ctx.alphaNeighbor j| - |0 - ctx.alphaNeighbor j|)| ≤ |a - 0| := by
    simpa using abs_abs_sub_abs_le_abs_sub
      (a - ctx.alphaNeighbor j) (0 - ctx.alphaNeighbor j)
  have hEq :
      (ctx.withAlphaCenter a).neighborWeight j - (binaryZeroCtx ctx).neighborWeight j =
        ctx.omega * (|a - ctx.alphaNeighbor j| - |0 - ctx.alphaNeighbor j|) := by
    simp [LocalContext.neighborWeight, LocalContext.withAlphaCenter, binaryZeroCtx]
    ring_nf
  calc
    |(ctx.withAlphaCenter a).neighborWeight j - (binaryZeroCtx ctx).neighborWeight j|
        = |ctx.omega * (|a - ctx.alphaNeighbor j| - |0 - ctx.alphaNeighbor j|)| := by
            rw [hEq]
    _ = ctx.omega * |(|a - ctx.alphaNeighbor j| - |0 - ctx.alphaNeighbor j|)| := by
      rw [abs_mul, abs_of_nonneg hω]
    _ ≤ ctx.omega * |a - 0| := by
      gcongr
    _ = ctx.omega * |a| := by simp

theorem totalWeight_sub_binaryZero_le
    (ctx : LocalContext ι)
    (a : ℝ)
    (hω : 0 ≤ ctx.omega) :
    |(ctx.withAlphaCenter a).totalWeight - (binaryZeroCtx ctx).totalWeight| ≤
      weightDriftBudget ctx |a| := by
  calc
    |(ctx.withAlphaCenter a).totalWeight - (binaryZeroCtx ctx).totalWeight|
        = |∑ j, ((ctx.withAlphaCenter a).neighborWeight j -
            (binaryZeroCtx ctx).neighborWeight j)| := by
            simp [LocalContext.totalWeight]
    _ ≤ ∑ j, |(ctx.withAlphaCenter a).neighborWeight j -
          (binaryZeroCtx ctx).neighborWeight j| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun j => (ctx.withAlphaCenter a).neighborWeight j -
              (binaryZeroCtx ctx).neighborWeight j) Finset.univ
    _ ≤ ∑ j, ctx.omega * |a| := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact neighborWeight_sub_binaryZero_le (ctx := ctx) a j hω
    _ = weightDriftBudget ctx |a| := by
      simp [weightDriftBudget]
      ring

theorem foregroundSum_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1) :
    0 ≤ ctx.foregroundSum ∧ ctx.foregroundSum ≤ ctx.totalWeight := by
  constructor
  · unfold LocalContext.foregroundSum
    refine Finset.sum_nonneg ?_
    intro j hj
    rcases hfg j with ⟨hj0, _⟩
    exact mul_nonneg (neighborWeight_nonneg ctx j) hj0
  · unfold LocalContext.foregroundSum LocalContext.totalWeight
    refine Finset.sum_le_sum ?_
    intro j hj
    rcases hfg j with ⟨hj0, hj1⟩
    have hw := neighborWeight_nonneg ctx j
    nlinarith

theorem backgroundSum_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    0 ≤ ctx.backgroundSum ∧ ctx.backgroundSum ≤ ctx.totalWeight := by
  constructor
  · unfold LocalContext.backgroundSum
    refine Finset.sum_nonneg ?_
    intro j hj
    rcases hbg j with ⟨hj0, _⟩
    exact mul_nonneg (neighborWeight_nonneg ctx j) hj0
  · unfold LocalContext.backgroundSum LocalContext.totalWeight
    refine Finset.sum_le_sum ?_
    intro j hj
    rcases hbg j with ⟨hj0, hj1⟩
    have hw := neighborWeight_nonneg ctx j
    nlinarith

theorem foregroundMean_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1) :
    0 ≤ ctx.foregroundMean ∧ ctx.foregroundMean ≤ 1 := by
  rcases foregroundSum_mem_Icc_of_boxedNeighbors (ctx := ctx) hfg with ⟨hs0, hs1⟩
  have htw : 0 < ctx.totalWeight := totalWeight_pos ctx
  constructor
  · exact div_nonneg hs0 htw.le
  · have h : ctx.foregroundSum / ctx.totalWeight ≤ ctx.totalWeight / ctx.totalWeight := by
      exact div_le_div_of_nonneg_right hs1 htw.le
    have hdiv : ctx.totalWeight / ctx.totalWeight = (1 : ℝ) := by
      exact div_self (show ctx.totalWeight ≠ 0 from htw.ne')
    calc
      ctx.foregroundMean = ctx.foregroundSum / ctx.totalWeight := rfl
      _ ≤ ctx.totalWeight / ctx.totalWeight := h
      _ = 1 := hdiv

theorem backgroundMean_mem_Icc_of_boxedNeighbors
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    0 ≤ ctx.backgroundMean ∧ ctx.backgroundMean ≤ 1 := by
  rcases backgroundSum_mem_Icc_of_boxedNeighbors (ctx := ctx) hbg with ⟨hs0, hs1⟩
  have htw : 0 < ctx.totalWeight := totalWeight_pos ctx
  constructor
  · exact div_nonneg hs0 htw.le
  · have h : ctx.backgroundSum / ctx.totalWeight ≤ ctx.totalWeight / ctx.totalWeight := by
      exact div_le_div_of_nonneg_right hs1 htw.le
    have hdiv : ctx.totalWeight / ctx.totalWeight = (1 : ℝ) := by
      exact div_self (show ctx.totalWeight ≠ 0 from htw.ne')
    calc
      ctx.backgroundMean = ctx.backgroundSum / ctx.totalWeight := rfl
      _ ≤ ctx.totalWeight / ctx.totalWeight := h
      _ = 1 := hdiv

theorem foreground_closedFormSolution_sub_foregroundMean_eq
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) - ctx.foregroundMean =
      ctx.alphaCenter *
        (ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
          ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean) /
        weightedMeanDenom ctx := by
  rw [foreground_closedFormSolution_eq_weightedMeanForm]
  field_simp [(weightedMeanDenom_pos ctx).ne']
  simp [closedFormForegroundMeanAffine, weightedMeanDenom]
  ring

theorem foreground_closedFormSolution_sub_foregroundMean_eq_meanResidualForm
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) - ctx.foregroundMean =
      ctx.alphaCenter * ctx.meanResidual / weightedMeanDenom ctx := by
  rw [foreground_closedFormSolution_sub_foregroundMean_eq]
  simp [FastMLFE2.Theory.Core.LocalContext.meanResidual]
  ring

theorem foreground_correction_uses_meanResidual
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) =
      ctx.foregroundMean +
        ctx.alphaCenter * ctx.meanResidual / weightedMeanDenom ctx := by
  calc
    foreground (closedFormSolution ctx)
        = ctx.foregroundMean +
            (foreground (closedFormSolution ctx) - ctx.foregroundMean) := by
              ring
    _ = ctx.foregroundMean +
          ctx.alphaCenter * ctx.meanResidual / weightedMeanDenom ctx := by
            rw [foreground_closedFormSolution_sub_foregroundMean_eq_meanResidualForm]

theorem background_closedFormSolution_sub_backgroundMean_eq
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) - ctx.backgroundMean =
      (1 - ctx.alphaCenter) *
        (ctx.imageValue - ctx.alphaCenter * ctx.foregroundMean -
          (1 - ctx.alphaCenter) * ctx.backgroundMean) /
        weightedMeanDenom ctx := by
  rw [background_closedFormSolution_eq_weightedMeanForm]
  field_simp [(weightedMeanDenom_pos ctx).ne']
  simp [closedFormBackgroundMeanAffine, weightedMeanDenom]
  ring

theorem background_closedFormSolution_sub_backgroundMean_eq_meanResidualForm
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) - ctx.backgroundMean =
      (1 - ctx.alphaCenter) * ctx.meanResidual / weightedMeanDenom ctx := by
  rw [background_closedFormSolution_sub_backgroundMean_eq]
  simp [FastMLFE2.Theory.Core.LocalContext.meanResidual]

theorem background_correction_uses_meanResidual
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) =
      ctx.backgroundMean +
        (1 - ctx.alphaCenter) * ctx.meanResidual / weightedMeanDenom ctx := by
  calc
    background (closedFormSolution ctx)
        = ctx.backgroundMean +
            (background (closedFormSolution ctx) - ctx.backgroundMean) := by
              ring
    _ = ctx.backgroundMean +
          (1 - ctx.alphaCenter) * ctx.meanResidual / weightedMeanDenom ctx := by
            rw [background_closedFormSolution_sub_backgroundMean_eq_meanResidualForm]

theorem meanResidual_corrections_of_solvesNormalEquation
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    {g : LocalUnknown}
    (hg : ctx.SolvesNormalEquation g) :
    foreground g =
        ctx.foregroundMean +
          ctx.alphaCenter * ctx.meanResidual / weightedMeanDenom ctx ∧
      background g =
        ctx.backgroundMean +
          (1 - ctx.alphaCenter) * ctx.meanResidual / weightedMeanDenom ctx := by
  have hclosed : g = closedFormSolution ctx :=
    eq_closedFormSolution_of_solvesNormalEquation (ctx := ctx) hg
  constructor
  · rw [hclosed]
    exact foreground_correction_uses_meanResidual ctx
  · rw [hclosed]
    exact background_correction_uses_meanResidual ctx

theorem abs_foreground_closedFormSolution_sub_foregroundMean_le
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |foreground (closedFormSolution ctx) - ctx.foregroundMean| ≤ 2 * ctx.alphaCenter := by
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  have hμF := foregroundMean_mem_Icc_of_boxedNeighbors (ctx := ctx) hfg
  have hμB := backgroundMean_mem_Icc_of_boxedNeighbors (ctx := ctx) hbg
  rw [foreground_closedFormSolution_sub_foregroundMean_eq]
  have hinner : |ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
      ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean| ≤ 1 := by
    have hlow : -1 ≤ ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
        ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean := by
      nlinarith [hI.1, hI.2, hα.1, hα.2, hμF.1, hμF.2, hμB.1, hμB.2]
    have hupp : ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
        ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean ≤ 1 := by
      nlinarith [hI.1, hI.2, hα.1, hα.2, hμF.1, hμF.2, hμB.1, hμB.2]
    exact abs_le.2 ⟨hlow, hupp⟩
  have hhalf : (1 : ℝ) / 2 ≤ weightedMeanDenom ctx := by
    have htw : 0 ≤ ctx.totalWeight := le_of_lt (totalWeight_pos ctx)
    have hsq : (1 : ℝ) / 2 ≤ ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 :=
      one_half_le_alphaQuadratic ctx
    have hdef : weightedMeanDenom ctx =
        ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) := by
      simp [weightedMeanDenom, add_assoc]
    nlinarith [hsq, htw, hdef]
  have hquot :
      |ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
        ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean| /
      weightedMeanDenom ctx ≤ 2 := by
    have hstep : |ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
        ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean|
        ≤ 2 * weightedMeanDenom ctx := by
      nlinarith [hinner, hhalf]
    have hden : 0 < weightedMeanDenom ctx := weightedMeanDenom_pos ctx
    calc
      |ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
          ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean| /
          weightedMeanDenom ctx
          ≤ (2 * weightedMeanDenom ctx) / weightedMeanDenom ctx := by
              exact div_le_div_of_nonneg_right hstep hden.le
      _ = 2 := by field_simp [hden.ne']
  calc
    |ctx.alphaCenter *
        (ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
          ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean) /
        weightedMeanDenom ctx|
        = ctx.alphaCenter *
          (|ctx.imageValue + ctx.alphaCenter * ctx.backgroundMean -
            ctx.alphaCenter * ctx.foregroundMean - ctx.backgroundMean| /
            weightedMeanDenom ctx) := by
              rw [div_eq_mul_inv]
              rw [div_eq_mul_inv, abs_mul, abs_mul, abs_inv]
              simp only [abs_of_nonneg hα.1, abs_of_pos (weightedMeanDenom_pos ctx)]
              ring
    _ ≤ ctx.alphaCenter * 2 := by
      gcongr
      exact hα.1
    _ = 2 * ctx.alphaCenter := by ring

end LocalContext

end FastMLFE2.Theory.Theorems
