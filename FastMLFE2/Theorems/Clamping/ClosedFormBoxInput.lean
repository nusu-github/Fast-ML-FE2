import FastMLFE2.Theorems.Clamping.ClosedFormBox

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def closedFormForegroundMeanAffine (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter * ctx.imageValue +
    (((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) *
        FastMLFE2.Core.LocalContext.foregroundMean ctx -
      ctx.alphaCenter * (1 - ctx.alphaCenter) *
        FastMLFE2.Core.LocalContext.backgroundMean ctx)

noncomputable def closedFormBackgroundMeanAffine (ctx : LocalContext ι) : ℝ :=
  (1 - ctx.alphaCenter) * ctx.imageValue +
    ((ctx.alphaCenter ^ 2 + ctx.totalWeight) *
        FastMLFE2.Core.LocalContext.backgroundMean ctx -
      ctx.alphaCenter * (1 - ctx.alphaCenter) *
        FastMLFE2.Core.LocalContext.foregroundMean ctx)

noncomputable def naiveBoxInputCounterexampleCtx : LocalContext PUnit where
  alphaCenter := (1 : ℝ) / 8
  imageValue := 0
  alphaNeighbor := fun _ => 0
  fgNeighbor := fun _ => 0
  bgNeighbor := fun _ => (1 : ℝ) / 8
  epsilonR := (1 : ℝ) / 2
  omega := 0

theorem naiveBoxInputCounterexample_has_boxed_inputs :
    (0 ≤ naiveBoxInputCounterexampleCtx.imageValue ∧
        naiveBoxInputCounterexampleCtx.imageValue ≤ 1) ∧
      (0 ≤ naiveBoxInputCounterexampleCtx.alphaCenter ∧
        naiveBoxInputCounterexampleCtx.alphaCenter ≤ 1) ∧
      (∀ j, 0 ≤ naiveBoxInputCounterexampleCtx.fgNeighbor j ∧
        naiveBoxInputCounterexampleCtx.fgNeighbor j ≤ 1) ∧
      (∀ j, 0 ≤ naiveBoxInputCounterexampleCtx.bgNeighbor j ∧
        naiveBoxInputCounterexampleCtx.bgNeighbor j ≤ 1) := by
  constructor
  · norm_num [naiveBoxInputCounterexampleCtx]
  constructor
  · norm_num [naiveBoxInputCounterexampleCtx]
  exact ⟨fun j => ⟨by simp [naiveBoxInputCounterexampleCtx],
                     by simp [naiveBoxInputCounterexampleCtx]⟩,
         fun j => ⟨by norm_num [naiveBoxInputCounterexampleCtx],
                   by norm_num [naiveBoxInputCounterexampleCtx]⟩⟩

theorem closedFormForegroundNumerator_naiveBoxInputCounterexample :
    closedFormForegroundNumerator naiveBoxInputCounterexampleCtx = -((7 : ℝ) / 1024) := by
  norm_num [naiveBoxInputCounterexampleCtx, closedFormForegroundNumerator,
    LocalContext.rhs, LocalContext.foregroundSum, LocalContext.backgroundSum,
    LocalContext.totalWeight, LocalContext.neighborWeight, foreground, background, mkLocalUnknown]

theorem closedFormForegroundNumerator_naiveBoxInputCounterexample_neg :
    closedFormForegroundNumerator naiveBoxInputCounterexampleCtx < 0 := by
  rw [closedFormForegroundNumerator_naiveBoxInputCounterexample]; norm_num

theorem not_naive_boxed_input_implies_foregroundNumerator_nonneg :
    ¬ ∀ {κ : Type*} [Fintype κ] (ctx : LocalContext κ),
        (0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1) →
        (0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) →
        (∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1) →
        (∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) →
        0 ≤ closedFormForegroundNumerator ctx := by
  intro h
  rcases naiveBoxInputCounterexample_has_boxed_inputs with ⟨hI, hα, hfg, hbg⟩
  linarith [h naiveBoxInputCounterexampleCtx hI hα hfg hbg,
    closedFormForegroundNumerator_naiveBoxInputCounterexample_neg]

theorem closedFormDenom_eq_totalWeight_mul_weightedMeanDenom (ctx : LocalContext ι) :
    closedFormDenom ctx = ctx.totalWeight * ctx.weightedMeanDenom := by
  simp [closedFormDenom, LocalContext.weightedMeanDenom]

theorem totalWeight_mul_foregroundMean
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.totalWeight * FastMLFE2.Core.LocalContext.foregroundMean ctx = ctx.foregroundSum := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  rw [FastMLFE2.Core.LocalContext.foregroundMean]; field_simp [htw0]

theorem totalWeight_mul_backgroundMean
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.totalWeight * FastMLFE2.Core.LocalContext.backgroundMean ctx = ctx.backgroundSum := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  rw [FastMLFE2.Core.LocalContext.backgroundMean]; field_simp [htw0]

theorem closedFormForegroundNumerator_eq_totalWeight_mul_meanAffine
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    closedFormForegroundNumerator ctx =
      ctx.totalWeight * closedFormForegroundMeanAffine ctx := by
  rw [closedFormForegroundNumerator, LocalContext.rhs_foreground, LocalContext.rhs_background,
    ← totalWeight_mul_foregroundMean ctx, ← totalWeight_mul_backgroundMean ctx]
  simp [closedFormForegroundMeanAffine]; ring

theorem closedFormBackgroundNumerator_eq_totalWeight_mul_meanAffine
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    closedFormBackgroundNumerator ctx =
      ctx.totalWeight * closedFormBackgroundMeanAffine ctx := by
  rw [closedFormBackgroundNumerator, LocalContext.rhs_foreground, LocalContext.rhs_background,
    ← totalWeight_mul_foregroundMean ctx, ← totalWeight_mul_backgroundMean ctx]
  simp [closedFormBackgroundMeanAffine]; ring

theorem foreground_closedFormSolution_eq_weightedMeanForm
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) =
      closedFormForegroundMeanAffine ctx / ctx.weightedMeanDenom := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have hred0 : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'
  rw [foreground_closedFormSolution, closedFormForegroundNumerator_eq_totalWeight_mul_meanAffine,
    closedFormDenom_eq_totalWeight_mul_weightedMeanDenom]
  field_simp [htw0, hred0]

theorem background_closedFormSolution_eq_weightedMeanForm
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) =
      closedFormBackgroundMeanAffine ctx / ctx.weightedMeanDenom := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have hred0 : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'
  rw [background_closedFormSolution, closedFormBackgroundNumerator_eq_totalWeight_mul_meanAffine,
    closedFormDenom_eq_totalWeight_mul_weightedMeanDenom]
  field_simp [htw0, hred0]

private theorem div_mem_unitInterval_iff {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {x d : α} (hd : 0 < d) :
    (0 ≤ x / d ∧ x / d ≤ 1) ↔ (0 ≤ x ∧ x ≤ d) := by
  rw [div_nonneg_iff]; constructor
  · rintro ⟨hx0 | hx0, hx1⟩
    · exact ⟨hx0.1, (div_le_one hd).1 hx1⟩
    · linarith [hx0.2]
  · rintro ⟨hx0, hx1⟩
    exact ⟨Or.inl ⟨hx0, hd.le⟩, (div_le_one hd).2 hx1⟩

theorem closedForm_foreground_mem_Icc_iff_weightedMeanBounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    (0 ≤ foreground (closedFormSolution ctx) ∧
        foreground (closedFormSolution ctx) ≤ 1) ↔
      (0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom) := by
  rw [foreground_closedFormSolution_eq_weightedMeanForm]
  exact div_mem_unitInterval_iff (weightedMeanDenom_pos ctx)

theorem closedForm_background_mem_Icc_iff_weightedMeanBounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    (0 ≤ background (closedFormSolution ctx) ∧
        background (closedFormSolution ctx) ≤ 1) ↔
      (0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) := by
  rw [background_closedFormSolution_eq_weightedMeanForm]
  exact div_mem_unitInterval_iff (weightedMeanDenom_pos ctx)

theorem closedForm_mem_box_iff_weightedMeanBounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    (0 ≤ foreground (closedFormSolution ctx) ∧
        foreground (closedFormSolution ctx) ≤ 1) ∧
      (0 ≤ background (closedFormSolution ctx) ∧
        background (closedFormSolution ctx) ≤ 1) ↔
      (0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom) ∧
      (0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) :=
  and_congr (closedForm_foreground_mem_Icc_iff_weightedMeanBounds ctx)
    (closedForm_background_mem_Icc_iff_weightedMeanBounds ctx)

theorem closedForm_clamp01_eq_self_iff_weightedMeanBounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx ↔
      (0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom) ∧
      (0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) :=
  (clamp01_eq_self_iff (g := closedFormSolution ctx)).trans
    (closedForm_mem_box_iff_weightedMeanBounds ctx)

theorem closedForm_clamp01_eq_self_of_weightedMeanBounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : 0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom)
    (hbg : 0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx :=
  (closedForm_clamp01_eq_self_iff_weightedMeanBounds ctx).2 ⟨hfg, hbg⟩

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg : 0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom)
    (hbg : 0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  simpa using closedForm_clamp01_eq_self_of_weightedMeanBounds ctx hfg hbg

end LocalContext

end FastMLFE2.Theorems
