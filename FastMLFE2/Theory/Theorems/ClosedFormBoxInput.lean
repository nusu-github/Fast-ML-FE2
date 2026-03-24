import FastMLFE2.Theory.Theorems.ClosedFormBox

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def closedFormForegroundMeanAffine (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter * ctx.imageValue +
    (((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) *
        FastMLFE2.Theory.Core.LocalContext.foregroundMean ctx -
      ctx.alphaCenter * (1 - ctx.alphaCenter) *
        FastMLFE2.Theory.Core.LocalContext.backgroundMean ctx)

noncomputable def closedFormBackgroundMeanAffine (ctx : LocalContext ι) : ℝ :=
  (1 - ctx.alphaCenter) * ctx.imageValue +
    ((ctx.alphaCenter ^ 2 + ctx.totalWeight) *
        FastMLFE2.Theory.Core.LocalContext.backgroundMean ctx -
      ctx.alphaCenter * (1 - ctx.alphaCenter) *
        FastMLFE2.Theory.Core.LocalContext.foregroundMean ctx)

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
  constructor
  · intro j
    have : naiveBoxInputCounterexampleCtx.fgNeighbor j = 0 := by
      simp [naiveBoxInputCounterexampleCtx]
    constructor <;> linarith
  · intro j
    have : naiveBoxInputCounterexampleCtx.bgNeighbor j = (1 : ℝ) / 8 := by
      simp [naiveBoxInputCounterexampleCtx]
    constructor <;> linarith

theorem closedFormForegroundNumerator_naiveBoxInputCounterexample :
    closedFormForegroundNumerator naiveBoxInputCounterexampleCtx = -((7 : ℝ) / 1024) := by
  norm_num [naiveBoxInputCounterexampleCtx, closedFormForegroundNumerator,
    FastMLFE2.Theory.Core.LocalContext.rhs,
    FastMLFE2.Theory.Core.LocalContext.foregroundSum,
    FastMLFE2.Theory.Core.LocalContext.backgroundSum,
    FastMLFE2.Theory.Core.LocalContext.totalWeight,
    FastMLFE2.Theory.Core.LocalContext.neighborWeight, foreground, background, mkLocalUnknown]

theorem closedFormForegroundNumerator_naiveBoxInputCounterexample_neg :
    closedFormForegroundNumerator naiveBoxInputCounterexampleCtx < 0 := by
  rw [closedFormForegroundNumerator_naiveBoxInputCounterexample]
  norm_num

theorem not_naive_boxed_input_implies_foregroundNumerator_nonneg :
    ¬ ∀ {κ : Type*} [Fintype κ] (ctx : LocalContext κ),
        (0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1) →
        (0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) →
        (∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1) →
        (∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) →
        0 ≤ closedFormForegroundNumerator ctx := by
  intro h
  rcases naiveBoxInputCounterexample_has_boxed_inputs with ⟨hI, hα, hfg, hbg⟩
  have hnum :
      0 ≤ closedFormForegroundNumerator naiveBoxInputCounterexampleCtx := by
    exact h naiveBoxInputCounterexampleCtx hI hα hfg hbg
  linarith [closedFormForegroundNumerator_naiveBoxInputCounterexample_neg]

theorem closedFormDenom_eq_totalWeight_mul_weightedMeanDenom (ctx : LocalContext ι) :
    closedFormDenom ctx = ctx.totalWeight * ctx.weightedMeanDenom := by
  simp [closedFormDenom, LocalContext.weightedMeanDenom]

theorem totalWeight_mul_foregroundMean
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    ctx.totalWeight * FastMLFE2.Theory.Core.LocalContext.foregroundMean ctx =
      ctx.foregroundSum := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  rw [FastMLFE2.Theory.Core.LocalContext.foregroundMean]
  field_simp [htw0]

theorem totalWeight_mul_backgroundMean
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    ctx.totalWeight * FastMLFE2.Theory.Core.LocalContext.backgroundMean ctx =
      ctx.backgroundSum := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  rw [FastMLFE2.Theory.Core.LocalContext.backgroundMean]
  field_simp [htw0]

theorem closedFormForegroundNumerator_eq_totalWeight_mul_meanAffine
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    closedFormForegroundNumerator ctx =
      ctx.totalWeight * closedFormForegroundMeanAffine ctx := by
  rw [closedFormForegroundNumerator,
    FastMLFE2.Theory.Core.LocalContext.rhs_foreground,
    FastMLFE2.Theory.Core.LocalContext.rhs_background]
  rw [← totalWeight_mul_foregroundMean (ctx := ctx),
    ← totalWeight_mul_backgroundMean (ctx := ctx)]
  simp [closedFormForegroundMeanAffine]
  ring

theorem closedFormBackgroundNumerator_eq_totalWeight_mul_meanAffine
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    closedFormBackgroundNumerator ctx =
      ctx.totalWeight * closedFormBackgroundMeanAffine ctx := by
  rw [closedFormBackgroundNumerator,
    FastMLFE2.Theory.Core.LocalContext.rhs_foreground,
    FastMLFE2.Theory.Core.LocalContext.rhs_background]
  rw [← totalWeight_mul_foregroundMean (ctx := ctx),
    ← totalWeight_mul_backgroundMean (ctx := ctx)]
  simp [closedFormBackgroundMeanAffine]
  ring

theorem foreground_closedFormSolution_eq_weightedMeanForm
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    foreground (closedFormSolution ctx) =
      closedFormForegroundMeanAffine ctx / ctx.weightedMeanDenom := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have hred0 : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'
  rw [foreground_closedFormSolution,
    closedFormForegroundNumerator_eq_totalWeight_mul_meanAffine,
    closedFormDenom_eq_totalWeight_mul_weightedMeanDenom]
  field_simp [htw0, hred0]

theorem background_closedFormSolution_eq_weightedMeanForm
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    background (closedFormSolution ctx) =
      closedFormBackgroundMeanAffine ctx / ctx.weightedMeanDenom := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have hred0 : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'
  rw [background_closedFormSolution,
    closedFormBackgroundNumerator_eq_totalWeight_mul_meanAffine,
    closedFormDenom_eq_totalWeight_mul_weightedMeanDenom]
  field_simp [htw0, hred0]

private theorem div_mem_unitInterval_iff
    {x d : ℝ}
    (hd : 0 < d) :
    (0 ≤ x / d ∧ x / d ≤ 1) ↔ (0 ≤ x ∧ x ≤ d) := by
  constructor
  · rintro ⟨hx0, hx1⟩
    constructor
    · by_contra hxneg
      have : x / d < 0 := by
        exact div_neg_of_neg_of_pos (lt_of_not_ge hxneg) hd
      linarith
    · by_contra hxd
      have : 1 < x / d := by
        have : d / d < x / d := by
          exact (div_lt_div_of_pos_right (lt_of_not_ge hxd) hd)
        simpa [hd.ne'] using this
      linarith
  · rintro ⟨hx0, hx1⟩
    constructor
    · exact div_nonneg hx0 hd.le
    · have hdiv : x / d ≤ d / d := by
        exact div_le_div_of_nonneg_right hx1 hd.le
      simpa [hd.ne'] using hdiv

theorem closedForm_foreground_mem_Icc_iff_weightedMeanBounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    (0 ≤ foreground (closedFormSolution ctx) ∧
        foreground (closedFormSolution ctx) ≤ 1) ↔
      (0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom) := by
  rw [foreground_closedFormSolution_eq_weightedMeanForm]
  exact div_mem_unitInterval_iff (weightedMeanDenom_pos ctx)

theorem closedForm_background_mem_Icc_iff_weightedMeanBounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    (0 ≤ background (closedFormSolution ctx) ∧
        background (closedFormSolution ctx) ≤ 1) ↔
      (0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) := by
  rw [background_closedFormSolution_eq_weightedMeanForm]
  exact div_mem_unitInterval_iff (weightedMeanDenom_pos ctx)

theorem closedForm_mem_box_iff_weightedMeanBounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    (0 ≤ foreground (closedFormSolution ctx) ∧
        foreground (closedFormSolution ctx) ≤ 1) ∧
      (0 ≤ background (closedFormSolution ctx) ∧
        background (closedFormSolution ctx) ≤ 1) ↔
      (0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom) ∧
      (0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) := by
  constructor <;> intro h
  · exact ⟨
      (closedForm_foreground_mem_Icc_iff_weightedMeanBounds (ctx := ctx)).1 h.1,
      (closedForm_background_mem_Icc_iff_weightedMeanBounds (ctx := ctx)).1 h.2⟩
  · exact ⟨
      (closedForm_foreground_mem_Icc_iff_weightedMeanBounds (ctx := ctx)).2 h.1,
      (closedForm_background_mem_Icc_iff_weightedMeanBounds (ctx := ctx)).2 h.2⟩

theorem closedForm_clamp01_eq_self_iff_weightedMeanBounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx ↔
      (0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom) ∧
      (0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) := by
  exact (clamp01_eq_self_iff (g := closedFormSolution ctx)).trans
    (closedForm_mem_box_iff_weightedMeanBounds (ctx := ctx))

theorem closedForm_clamp01_eq_self_of_weightedMeanBounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hfg :
      0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom)
    (hbg :
      0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  exact (closedForm_clamp01_eq_self_iff_weightedMeanBounds (ctx := ctx)).2 ⟨hfg, hbg⟩

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg :
      0 ≤ closedFormForegroundMeanAffine ctx ∧
        closedFormForegroundMeanAffine ctx ≤ ctx.weightedMeanDenom)
    (hbg :
      0 ≤ closedFormBackgroundMeanAffine ctx ∧
        closedFormBackgroundMeanAffine ctx ≤ ctx.weightedMeanDenom) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  simpa using closedForm_clamp01_eq_self_of_weightedMeanBounds (ctx := ctx) hfg hbg

end LocalContext

end FastMLFE2.Theory.Theorems
