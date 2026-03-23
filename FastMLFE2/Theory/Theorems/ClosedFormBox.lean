import FastMLFE2.Theory.Theorems.ClampLocal

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem closedForm_foreground_mem_Icc_of_numerator_bounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hfg :
      0 ≤ closedFormForegroundNumerator ctx ∧
        closedFormForegroundNumerator ctx ≤ closedFormDenom ctx) :
    0 ≤ foreground (closedFormSolution ctx) ∧
      foreground (closedFormSolution ctx) ≤ 1 := by
  have hden := closedFormDenom_pos ctx
  rw [foreground_closedFormSolution]
  exact ⟨div_nonneg hfg.1 hden.le,
    (div_le_one hden).mpr hfg.2⟩

theorem closedForm_background_mem_Icc_of_numerator_bounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hbg :
      0 ≤ closedFormBackgroundNumerator ctx ∧
        closedFormBackgroundNumerator ctx ≤ closedFormDenom ctx) :
    0 ≤ background (closedFormSolution ctx) ∧
      background (closedFormSolution ctx) ≤ 1 := by
  have hden := closedFormDenom_pos ctx
  rw [background_closedFormSolution]
  exact ⟨div_nonneg hbg.1 hden.le,
    (div_le_one hden).mpr hbg.2⟩

theorem closedForm_clamp01_eq_self_of_numerator_bounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hfg :
      0 ≤ closedFormForegroundNumerator ctx ∧
        closedFormForegroundNumerator ctx ≤ closedFormDenom ctx)
    (hbg :
      0 ≤ closedFormBackgroundNumerator ctx ∧
        closedFormBackgroundNumerator ctx ≤ closedFormDenom ctx) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  obtain ⟨hfg0, hfg1⟩ := closedForm_foreground_mem_Icc_of_numerator_bounds ctx hfg
  obtain ⟨hbg0, hbg1⟩ := closedForm_background_mem_Icc_of_numerator_bounds ctx hbg
  exact closedForm_clamp01_eq_self_of_component_bounds ctx hfg0 hfg1 hbg0 hbg1

theorem closedForm_clamp01_eq_self_of_exists_boxed_solution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hex : ∃ g : LocalUnknown, ctx.SolvesNormalEquation g ∧ clamp01 g = g) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  rcases hex with ⟨g, hgsolve, hgclamp⟩
  rwa [eq_inverseSolution_of_solves ctx hgsolve, ← closedForm_eq_inverseSolution] at hgclamp

theorem closedForm_mem_box_of_exists_boxed_solution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hex : ∃ g : LocalUnknown, ctx.SolvesNormalEquation g ∧ clamp01 g = g) :
    (0 ≤ foreground (closedFormSolution ctx) ∧ foreground (closedFormSolution ctx) ≤ 1) ∧
      (0 ≤ background (closedFormSolution ctx) ∧ background (closedFormSolution ctx) ≤ 1) :=
  (clamp01_eq_self_iff _).1 (closedForm_clamp01_eq_self_of_exists_boxed_solution ctx hex)

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg :
      0 ≤ closedFormForegroundNumerator ctx ∧
        closedFormForegroundNumerator ctx ≤ closedFormDenom ctx)
    (hbg :
      0 ≤ closedFormBackgroundNumerator ctx ∧
        closedFormBackgroundNumerator ctx ≤ closedFormDenom ctx) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx :=
  closedForm_clamp01_eq_self_of_numerator_bounds ctx hfg hbg

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hex : ∃ g : LocalUnknown, ctx.SolvesNormalEquation g ∧ clamp01 g = g) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx :=
  closedForm_clamp01_eq_self_of_exists_boxed_solution ctx hex

end LocalContext

end FastMLFE2.Theory.Theorems
