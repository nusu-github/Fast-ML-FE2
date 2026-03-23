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
  rcases hfg with ⟨hfg0, hfg1⟩
  have hden : 0 < closedFormDenom ctx := closedFormDenom_pos ctx
  constructor
  · rw [foreground_closedFormSolution]
    exact div_nonneg hfg0 hden.le
  · rw [foreground_closedFormSolution]
    have hden0 : 0 ≤ closedFormDenom ctx := hden.le
    have hle : closedFormForegroundNumerator ctx / closedFormDenom ctx ≤
        closedFormDenom ctx / closedFormDenom ctx := by
      exact div_le_div_of_nonneg_right hfg1 hden0
    have hdiv : closedFormDenom ctx / closedFormDenom ctx = 1 := by
      exact div_self (show closedFormDenom ctx ≠ 0 from hden.ne')
    simpa [hdiv] using hle

theorem closedForm_background_mem_Icc_of_numerator_bounds
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hbg :
      0 ≤ closedFormBackgroundNumerator ctx ∧
        closedFormBackgroundNumerator ctx ≤ closedFormDenom ctx) :
    0 ≤ background (closedFormSolution ctx) ∧
      background (closedFormSolution ctx) ≤ 1 := by
  rcases hbg with ⟨hbg0, hbg1⟩
  have hden : 0 < closedFormDenom ctx := closedFormDenom_pos ctx
  constructor
  · rw [background_closedFormSolution]
    exact div_nonneg hbg0 hden.le
  · rw [background_closedFormSolution]
    have hden0 : 0 ≤ closedFormDenom ctx := hden.le
    have hle : closedFormBackgroundNumerator ctx / closedFormDenom ctx ≤
        closedFormDenom ctx / closedFormDenom ctx := by
      exact div_le_div_of_nonneg_right hbg1 hden0
    have hdiv : closedFormDenom ctx / closedFormDenom ctx = 1 := by
      exact div_self (show closedFormDenom ctx ≠ 0 from hden.ne')
    simpa [hdiv] using hle

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
  obtain ⟨hfg0, hfg1⟩ := closedForm_foreground_mem_Icc_of_numerator_bounds (ctx := ctx) hfg
  obtain ⟨hbg0, hbg1⟩ := closedForm_background_mem_Icc_of_numerator_bounds (ctx := ctx) hbg
  exact closedForm_clamp01_eq_self_of_component_bounds (ctx := ctx) hfg0 hfg1 hbg0 hbg1

theorem closedForm_clamp01_eq_self_of_exists_boxed_solution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hex : ∃ g : LocalUnknown, ctx.SolvesNormalEquation g ∧ clamp01 g = g) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  rcases hex with ⟨g, hgsolve, hgclamp⟩
  have hgEqInv : g = inverseSolution ctx := eq_inverseSolution_of_solves ctx hgsolve
  have hcfEqInv : closedFormSolution ctx = inverseSolution ctx := closedForm_eq_inverseSolution ctx
  have hgEqCf : g = closedFormSolution ctx := by
    rw [hgEqInv, ← hcfEqInv]
  simpa [hgEqCf] using hgclamp

theorem closedForm_mem_box_of_exists_boxed_solution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hex : ∃ g : LocalUnknown, ctx.SolvesNormalEquation g ∧ clamp01 g = g) :
    (0 ≤ foreground (closedFormSolution ctx) ∧ foreground (closedFormSolution ctx) ≤ 1) ∧
      (0 ≤ background (closedFormSolution ctx) ∧ background (closedFormSolution ctx) ≤ 1) := by
  exact (clamp01_eq_self_iff (g := closedFormSolution ctx)).1
    (closedForm_clamp01_eq_self_of_exists_boxed_solution (ctx := ctx) hex)

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hfg :
      0 ≤ closedFormForegroundNumerator ctx ∧
        closedFormForegroundNumerator ctx ≤ closedFormDenom ctx)
    (hbg :
      0 ≤ closedFormBackgroundNumerator ctx ∧
        closedFormBackgroundNumerator ctx ≤ closedFormDenom ctx) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  simpa using closedForm_clamp01_eq_self_of_numerator_bounds (ctx := ctx) hfg hbg

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hex : ∃ g : LocalUnknown, ctx.SolvesNormalEquation g ∧ clamp01 g = g) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  simpa using closedForm_clamp01_eq_self_of_exists_boxed_solution (ctx := ctx) hex

end LocalContext

end FastMLFE2.Theory.Theorems
