import FastMLFE2.Core.ClosedForm
import FastMLFE2.Core.LocalSemantics
import FastMLFE2.Theorems.Invertibility
import FastMLFE2.Theorems.CostToNormalEquation

namespace FastMLFE2.Theorems

/-!
Closed-form correctness theorems for the 2×2 local normal equation.

The definitions (`closedFormSolution`, `closedFormDenom`, etc.) live in `Core.ClosedForm`.
This file proves they actually solve the normal equation and are cost-stationary.
-/

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

export FastMLFE2.Core.LocalContext (closedFormDenom closedFormForegroundNumerator
  closedFormBackgroundNumerator closedFormSolution inverseSolution
  foreground_closedFormSolution background_closedFormSolution)

variable {ι : Type*} [Fintype ι]

private theorem solve2x2_foreground
    {a00 a01 a11 b0 b1 det : ℝ}
    (hdet : det = a00 * a11 - a01 * a01) (hdet0 : det ≠ 0) :
    a00 * ((a11 * b0 - a01 * b1) / det) +
        a01 * ((a00 * b1 - a01 * b0) / det) = b0 := by
  field_simp [hdet0]; rw [hdet]; ring

private theorem solve2x2_background
    {a00 a01 a11 b0 b1 det : ℝ}
    (hdet : det = a00 * a11 - a01 * a01) (hdet0 : det ≠ 0) :
    a01 * ((a11 * b0 - a01 * b1) / det) +
        a11 * ((a00 * b1 - a01 * b0) / det) = b1 := by
  field_simp [hdet0]; rw [hdet]; ring

theorem closedFormDenom_eq_det (ctx : LocalContext ι) :
    closedFormDenom ctx = ctx.normalMatrix.det := by
  simpa [closedFormDenom] using (normalMatrix_det ctx).symm

theorem closedFormDenom_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < closedFormDenom ctx := by
  rw [closedFormDenom_eq_det]; exact normalMatrix_det_pos ctx

theorem inverseSolution_solvesNormalEquation (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.SolvesNormalEquation (inverseSolution ctx) := by
  dsimp [LocalContext.SolvesNormalEquation, inverseSolution]
  rw [Matrix.mulVec_mulVec]
  simpa [Matrix.one_mulVec] using
    congrArg (·.mulVec ctx.rhs) (Matrix.mul_nonsing_inv _ (normalMatrix_det_isUnit ctx))

private theorem closedFormDenom_eq_minor (ctx : LocalContext ι) :
    closedFormDenom ctx =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight) * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) -
        (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 := by
  simp [closedFormDenom]; ring

theorem closedForm_foreground_solves (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.mulVec (closedFormSolution ctx) 0 = ctx.rhs 0 := by
  simpa [closedFormSolution, foreground, background] using
    solve2x2_foreground
      (by simpa [pow_two] using closedFormDenom_eq_minor ctx)
      (closedFormDenom_pos ctx).ne'

theorem closedForm_background_solves (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.mulVec (closedFormSolution ctx) 1 = ctx.rhs 1 := by
  simpa [closedFormSolution, foreground, background] using
    solve2x2_background
      (by simpa [pow_two] using closedFormDenom_eq_minor ctx)
      (closedFormDenom_pos ctx).ne'

theorem eq_inverseSolution_of_solves (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    {g : LocalUnknown} (hg : ctx.SolvesNormalEquation g) :
    g = inverseSolution ctx := by
  have hunit := normalMatrix_det_isUnit ctx
  have : (ctx.normalMatrix⁻¹ * ctx.normalMatrix).mulVec g = inverseSolution ctx := by
    simpa [inverseSolution, LocalContext.SolvesNormalEquation, Matrix.mulVec_mulVec] using
      congrArg ctx.normalMatrix⁻¹.mulVec hg
  rwa [Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec] at this

theorem closedForm_solvesNormalEquation (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.SolvesNormalEquation (closedFormSolution ctx) := by
  funext i; fin_cases i
  · exact closedForm_foreground_solves ctx
  · exact closedForm_background_solves ctx

theorem closedForm_eq_inverseSolution (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    closedFormSolution ctx = inverseSolution ctx :=
  eq_inverseSolution_of_solves ctx (closedForm_solvesNormalEquation ctx)

theorem eq_closedFormSolution_of_solvesNormalEquation
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    {g : LocalUnknown}
    (hg : ctx.SolvesNormalEquation g) :
    g = closedFormSolution ctx := by
  calc
    g = inverseSolution ctx := eq_inverseSolution_of_solves ctx hg
    _ = closedFormSolution ctx := (closedForm_eq_inverseSolution ctx).symm

theorem closedForm_isCostStationary (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.IsCostStationary (closedFormSolution ctx) :=
  (isCostStationary_iff_solvesNormalEquation ctx _).2 (closedForm_solvesNormalEquation ctx)

end LocalContext

end FastMLFE2.Theorems
