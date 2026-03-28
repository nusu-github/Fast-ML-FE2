import FastMLFE2.Theorems.Solvability.ClosedForm
import FastMLFE2.Theorems.Clamping.ClosedFormBoxInput
import FastMLFE2.Theorems.Iteration.JacobiContraction
import FastMLFE2.Theorems.Solvability.Invertibility
import FastMLFE2.Theorems.Solvability.Conditioning
import FastMLFE2.Theorems.Solvability.MeanResidualBounds

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

private theorem beta_div_denom_le_two_mul
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (β : ℝ) (hβ : 0 ≤ β) :
    β / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) ≤ 2 * β := by
  have hhalf : (1 : ℝ) / 2 ≤ ctx.totalWeight + β ^ 2 + (1 - β) ^ 2 := by
    nlinarith [totalWeight_pos ctx, alpha_sq_add_one_minus_alpha_sq_ge_half β]
  have hpos : 0 < ctx.totalWeight + β ^ 2 + (1 - β) ^ 2 := by linarith
  have h1D : 1 / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) ≤ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have hmul : β * (1 / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2)) ≤ β * 2 :=
    mul_le_mul_of_nonneg_left h1D hβ
  calc
    β / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) = β * (1 / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2)) := by
      simp [div_eq_mul_inv]
    _ ≤ β * 2 := hmul
    _ = 2 * β := by ring

private theorem coeffDiff_le_beta_div_denom
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    |(1 - β) / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) -
        1 / (ctx.totalWeight + 1)| ≤
      β / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) := by
  have hDpos : 0 < ctx.totalWeight + β ^ 2 + (1 - β) ^ 2 := by
    nlinarith [totalWeight_pos ctx, alpha_sq_add_one_minus_alpha_sq_ge_half β]
  have hW1pos : 0 < ctx.totalWeight + 1 := by linarith [totalWeight_pos ctx]
  have hnum : |1 - ctx.totalWeight - 2 * β| ≤ ctx.totalWeight + 1 := by
    refine abs_le.2 ?_
    constructor
    · nlinarith [hβ1]
    · nlinarith [hβ, le_of_lt (totalWeight_pos ctx)]
  have hEq :
      (1 - β) / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) - 1 / (ctx.totalWeight + 1) =
        β * (1 - ctx.totalWeight - 2 * β) /
          ((ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) * (ctx.totalWeight + 1)) := by
    field_simp [hDpos.ne', hW1pos.ne']
    ring
  rw [hEq, abs_div, abs_mul, abs_of_nonneg hβ, abs_of_pos (mul_pos hDpos hW1pos)]
  calc
    β * |1 - ctx.totalWeight - 2 * β| /
        ((ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) * (ctx.totalWeight + 1)) ≤
        β * (ctx.totalWeight + 1) /
          ((ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) * (ctx.totalWeight + 1)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum hβ)
        (le_of_lt (mul_pos hDpos hW1pos))
    _ = β / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) := by
      field_simp [hDpos.ne', hW1pos.ne']

private theorem crossTerm_le_beta_div_denom
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (β : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    |β * (1 - β) / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2)| ≤
      β / (ctx.totalWeight + β ^ 2 + (1 - β) ^ 2) := by
  have hDpos : 0 < ctx.totalWeight + β ^ 2 + (1 - β) ^ 2 := by
    nlinarith [totalWeight_pos ctx, alpha_sq_add_one_minus_alpha_sq_ge_half β]
  have h1mβ : 0 ≤ 1 - β := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hβ, abs_of_nonneg h1mβ, abs_of_pos hDpos]
  have hmul : β * (1 - β) ≤ β := by nlinarith [hβ, hβ1]
  exact div_le_div_of_nonneg_right hmul (le_of_lt hDpos)

theorem abs_background_closedFormSolution_sub_backgroundMean_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |background (closedFormSolution ctx) - ctx.backgroundMean| ≤
      2 * (1 - ctx.alphaCenter) := by
  have hbound := abs_background_correction_le ctx hI
    (CoreMathAssumptions.alphaCenterBounded (ctx := ctx)) hfg hbg
  rwa [← background_closedFormSolution_sub_backgroundMean_eq_meanResidualForm] at hbound

theorem abs_background_closedFormSolution_sub_backgroundMean_le_of_one_minus_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : 1 - ctx.alphaCenter ≤ τ) :
    |background (closedFormSolution ctx) - ctx.backgroundMean| ≤ 2 * τ := by
  have hbound := abs_background_closedFormSolution_sub_backgroundMean_le ctx hI hfg hbg
  have hτ : 2 * (1 - ctx.alphaCenter) ≤ 2 * τ := by nlinarith
  exact le_trans hbound hτ

theorem abs_background_closedFormSolution_sub_binaryZeroCtx_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |background (closedFormSolution ctx) -
        (ctx.backgroundMean +
          (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1))| ≤
      4 * ctx.alphaCenter := by
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  have hμF := foregroundMean_mem_Icc_of_boxedNeighbors ctx hfg
  have hμB := backgroundMean_mem_Icc_of_boxedNeighbors ctx hbg
  have hdiff :
      background (closedFormSolution ctx) -
        (ctx.backgroundMean +
          (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1)) =
        ((1 - ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
          (ctx.imageValue - ctx.backgroundMean) -
        (ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
          (ctx.foregroundMean - ctx.backgroundMean) := by
    rw [background_correction_uses_meanResidual ctx]
    simp [FastMLFE2.Core.LocalContext.meanResidual]
    ring
  have hcoeff0 :
      |(1 - ctx.alphaCenter) / ctx.weightedMeanDenom -
        1 / (ctx.totalWeight + 1)| ≤
        ctx.alphaCenter / ctx.weightedMeanDenom := by
    simpa [LocalContext.weightedMeanDenom] using
      coeffDiff_le_beta_div_denom (ctx := ctx) (β := ctx.alphaCenter) hα.1 hα.2
  have hcross0 :
      |ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom| ≤
        ctx.alphaCenter / ctx.weightedMeanDenom := by
    simpa [LocalContext.weightedMeanDenom] using
      crossTerm_le_beta_div_denom (ctx := ctx) (β := ctx.alphaCenter) hα.1 hα.2
  have hden : ctx.alphaCenter / ctx.weightedMeanDenom ≤ 2 * ctx.alphaCenter := by
    exact beta_div_denom_le_two_mul ctx ctx.alphaCenter hα.1
  have hcoeff : |(1 - ctx.alphaCenter) / ctx.weightedMeanDenom -
      1 / (ctx.totalWeight + 1)| ≤ 2 * ctx.alphaCenter :=
    le_trans hcoeff0 hden
  have hcross : |ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom| ≤
      2 * ctx.alphaCenter :=
    le_trans hcross0 hden
  have hIB : |ctx.imageValue - ctx.backgroundMean| ≤ 1 := by
    apply abs_le.2
    constructor <;> nlinarith [hI.1, hI.2, hμB.1, hμB.2]
  have hFB : |ctx.foregroundMean - ctx.backgroundMean| ≤ 1 := by
    apply abs_le.2
    constructor <;> nlinarith [hμF.1, hμF.2, hμB.1, hμB.2]
  have hterm1 :
      |((1 - ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
        (ctx.imageValue - ctx.backgroundMean)| ≤ 2 * ctx.alphaCenter := by
    rw [abs_mul]
    calc
      |(1 - ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)| *
          |ctx.imageValue - ctx.backgroundMean|
        ≤ (2 * ctx.alphaCenter) * 1 := by
          exact mul_le_mul hcoeff hIB (abs_nonneg _) (by nlinarith [hα.1])
      _ = 2 * ctx.alphaCenter := by ring
  have hterm2 :
      |(ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
        (ctx.foregroundMean - ctx.backgroundMean)| ≤ 2 * ctx.alphaCenter := by
    rw [abs_mul]
    calc
      |ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom| *
          |ctx.foregroundMean - ctx.backgroundMean|
        ≤ (2 * ctx.alphaCenter) * 1 := by
          exact mul_le_mul hcross hFB (abs_nonneg _) (by nlinarith [hα.1])
      _ = 2 * ctx.alphaCenter := by ring
  rw [hdiff]
  calc
    |((1 - ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
        (ctx.imageValue - ctx.backgroundMean) -
        (ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
          (ctx.foregroundMean - ctx.backgroundMean)| ≤
        |((1 - ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
          (ctx.imageValue - ctx.backgroundMean)| +
          |(ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
            (ctx.foregroundMean - ctx.backgroundMean)| := by
          simpa using
            (abs_sub_le
              (((1 - ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
                (ctx.imageValue - ctx.backgroundMean))
              0
              ((ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
                (ctx.foregroundMean - ctx.backgroundMean)))
    _ ≤ 2 * ctx.alphaCenter + 2 * ctx.alphaCenter := by
          exact add_le_add hterm1 hterm2
    _ = 4 * ctx.alphaCenter := by ring

theorem foreground_closedFormSolution_sub_binaryOneCtx_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |foreground (closedFormSolution ctx) -
        (ctx.foregroundMean +
          (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1))| ≤
      4 * (1 - ctx.alphaCenter) := by
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  have hμF := foregroundMean_mem_Icc_of_boxedNeighbors ctx hfg
  have hμB := backgroundMean_mem_Icc_of_boxedNeighbors ctx hbg
  have hdiff :
      foreground (closedFormSolution ctx) -
        (ctx.foregroundMean +
          (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1)) =
        ((ctx.alphaCenter) / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
          (ctx.imageValue - ctx.foregroundMean) -
        (ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
          (ctx.backgroundMean - ctx.foregroundMean) := by
    rw [foreground_correction_uses_meanResidual ctx]
    simp [FastMLFE2.Core.LocalContext.meanResidual]
    ring
  have hβ : 0 ≤ (1 - ctx.alphaCenter) := by linarith
  have hβ1 : 1 - ctx.alphaCenter ≤ 1 := by linarith
  have hcoeff0 :
      |ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)| ≤
        (1 - ctx.alphaCenter) / ctx.weightedMeanDenom := by
    simpa [LocalContext.weightedMeanDenom, add_comm, add_left_comm, add_assoc] using
      coeffDiff_le_beta_div_denom (ctx := ctx) (β := 1 - ctx.alphaCenter) hβ hβ1
  have hcross0 :
      |ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom| ≤
        (1 - ctx.alphaCenter) / ctx.weightedMeanDenom := by
    simpa [LocalContext.weightedMeanDenom, add_comm, add_left_comm, add_assoc, mul_comm] using
      crossTerm_le_beta_div_denom (ctx := ctx) (β := 1 - ctx.alphaCenter) hβ hβ1
  have hden : (1 - ctx.alphaCenter) / ctx.weightedMeanDenom ≤ 2 * (1 - ctx.alphaCenter) := by
    simpa [LocalContext.weightedMeanDenom, add_comm, add_left_comm, add_assoc] using
      beta_div_denom_le_two_mul ctx (1 - ctx.alphaCenter) hβ
  have hcoeff : |ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)| ≤
      2 * (1 - ctx.alphaCenter) :=
    le_trans hcoeff0 hden
  have hcross : |ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom| ≤
      2 * (1 - ctx.alphaCenter) :=
    le_trans hcross0 hden
  have hIF : |ctx.imageValue - ctx.foregroundMean| ≤ 1 := by
    apply abs_le.2
    constructor <;> nlinarith [hI.1, hI.2, hμF.1, hμF.2]
  have hBF : |ctx.backgroundMean - ctx.foregroundMean| ≤ 1 := by
    apply abs_le.2
    constructor <;> nlinarith [hμF.1, hμF.2, hμB.1, hμB.2]
  have hterm1 :
      |(ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
        (ctx.imageValue - ctx.foregroundMean)| ≤ 2 * (1 - ctx.alphaCenter) := by
    rw [abs_mul]
    calc
      |ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)| *
          |ctx.imageValue - ctx.foregroundMean|
        ≤ (2 * (1 - ctx.alphaCenter)) * 1 := by
          exact mul_le_mul hcoeff hIF (abs_nonneg _) (by nlinarith [hα.1])
      _ = 2 * (1 - ctx.alphaCenter) := by ring
  have hterm2 :
      |(ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
        (ctx.backgroundMean - ctx.foregroundMean)| ≤ 2 * (1 - ctx.alphaCenter) := by
    rw [abs_mul]
    calc
      |ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom| *
          |ctx.backgroundMean - ctx.foregroundMean|
        ≤ (2 * (1 - ctx.alphaCenter)) * 1 := by
          exact mul_le_mul hcross hBF (abs_nonneg _) (by nlinarith [hα.1])
      _ = 2 * (1 - ctx.alphaCenter) := by ring
  rw [hdiff]
  calc
    |(ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
        (ctx.imageValue - ctx.foregroundMean) -
        (ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
          (ctx.backgroundMean - ctx.foregroundMean)| ≤
        |(ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
          (ctx.imageValue - ctx.foregroundMean)| +
          |(ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
            (ctx.backgroundMean - ctx.foregroundMean)| := by
          simpa using
            (abs_sub_le
              ((ctx.alphaCenter / ctx.weightedMeanDenom - 1 / (ctx.totalWeight + 1)) *
                (ctx.imageValue - ctx.foregroundMean))
              0
              ((ctx.alphaCenter * (1 - ctx.alphaCenter) / ctx.weightedMeanDenom) *
                (ctx.backgroundMean - ctx.foregroundMean)))
    _ ≤ 2 * (1 - ctx.alphaCenter) + 2 * (1 - ctx.alphaCenter) := by
          exact add_le_add hterm1 hterm2
    _ = 4 * (1 - ctx.alphaCenter) := by ring

theorem foreground_closedFormSolution_sub_binaryZeroCtx_le_of_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : ctx.alphaCenter ≤ τ) :
    |foreground (closedFormSolution ctx) - ctx.foregroundMean| ≤ 2 * τ := by
  have hbound := abs_foreground_closedFormSolution_sub_foregroundMean_le ctx hI hfg hbg
  have hτ : 2 * ctx.alphaCenter ≤ 2 * τ := by nlinarith
  exact le_trans hbound hτ

theorem background_closedFormSolution_sub_binaryZeroCtx_le_of_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : ctx.alphaCenter ≤ τ) :
    |background (closedFormSolution ctx) -
        (ctx.backgroundMean +
          (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1))| ≤
      4 * τ := by
  have hbound := abs_background_closedFormSolution_sub_binaryZeroCtx_le ctx hI hfg hbg
  have hτ : 4 * ctx.alphaCenter ≤ 4 * τ := by nlinarith
  exact le_trans hbound hτ

theorem foreground_closedFormSolution_sub_binaryOneCtx_le_of_one_minus_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : 1 - ctx.alphaCenter ≤ τ) :
    |foreground (closedFormSolution ctx) -
        (ctx.foregroundMean +
          (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1))| ≤
      4 * τ := by
  have hbound := foreground_closedFormSolution_sub_binaryOneCtx_le ctx hI hfg hbg
  have hτ : 4 * (1 - ctx.alphaCenter) ≤ 4 * τ := by nlinarith
  exact le_trans hbound hτ

theorem background_closedFormSolution_sub_binaryOneCtx_le_of_one_minus_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : 1 - ctx.alphaCenter ≤ τ) :
    |background (closedFormSolution ctx) - ctx.backgroundMean| ≤ 2 * τ := by
  exact abs_background_closedFormSolution_sub_backgroundMean_le_of_one_minus_alpha_le_tau
    (ctx := ctx) hI hfg hbg hατ

theorem localInfinityNorm_sub_binaryZeroCtx_le_of_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : ctx.alphaCenter ≤ τ) :
    localInfinityNorm
        (closedFormSolution ctx -
          ![ctx.foregroundMean,
            ctx.backgroundMean +
              (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1)]) ≤
      4 * τ := by
  have hfg' := foreground_closedFormSolution_sub_binaryZeroCtx_le_of_alpha_le_tau
    (ctx := ctx) hI hfg hbg hατ
  have hbg' := background_closedFormSolution_sub_binaryZeroCtx_le_of_alpha_le_tau
    (ctx := ctx) hI hfg hbg hατ
  have hfg4 : |foreground (closedFormSolution ctx -
      ![ctx.foregroundMean,
        ctx.backgroundMean + (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1)])| ≤
      4 * τ := by
    have hτ : 2 * τ ≤ 4 * τ := by
      have hτ0 : 0 ≤ τ := by nlinarith [hατ, (CoreMathAssumptions.alphaCenterBounded (ctx := ctx)).1]
      nlinarith
    exact le_trans (by simpa [foreground] using hfg') hτ
  have hbg4 : |background (closedFormSolution ctx -
      ![ctx.foregroundMean,
        ctx.backgroundMean + (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1)])| ≤
      4 * τ := by
    simpa [background] using hbg'
  simpa [localInfinityNorm, foreground, background] using max_le hfg4 hbg4

theorem localInfinityNorm_sub_binaryOneCtx_le_of_one_minus_alpha_le_tau
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1)
    {τ : ℝ} (hατ : 1 - ctx.alphaCenter ≤ τ) :
    localInfinityNorm
        (closedFormSolution ctx -
          ![ctx.foregroundMean +
              (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1),
            ctx.backgroundMean]) ≤
      4 * τ := by
  have hfg' := foreground_closedFormSolution_sub_binaryOneCtx_le_of_one_minus_alpha_le_tau
    (ctx := ctx) hI hfg hbg hατ
  have hbg' := background_closedFormSolution_sub_binaryOneCtx_le_of_one_minus_alpha_le_tau
    (ctx := ctx) hI hfg hbg hατ
  have hfg4 : |foreground (closedFormSolution ctx -
      ![ctx.foregroundMean +
          (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1),
        ctx.backgroundMean])| ≤
      4 * τ := by
    simpa [foreground] using hfg'
  have hbg4 : |background (closedFormSolution ctx -
      ![ctx.foregroundMean +
          (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1),
        ctx.backgroundMean])| ≤
      4 * τ := by
    have hτ : 2 * τ ≤ 4 * τ := by
      have hτ0 : 0 ≤ τ := by
        nlinarith [hατ, (CoreMathAssumptions.alphaCenterBounded (ctx := ctx)).2]
      nlinarith
    exact le_trans (by simpa [background] using hbg') hτ
  simpa [localInfinityNorm, foreground, background] using max_le hfg4 hbg4

end LocalContext

end FastMLFE2.Theorems
