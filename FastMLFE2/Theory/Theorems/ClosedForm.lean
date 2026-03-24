import FastMLFE2.Theory.Core.LocalSemantics
import FastMLFE2.Theory.Theorems.Invertibility
import FastMLFE2.Theory.Theorems.CostToNormalEquation

namespace FastMLFE2.Theory.Theorems

/-!
Initial closed-form equivalence theorems for the local theory kernel.
-/

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

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

def closedFormDenom (ctx : LocalContext ι) : ℝ :=
  ctx.totalWeight * ctx.weightedMeanDenom

def closedFormForegroundNumerator (ctx : LocalContext ι) : ℝ :=
  ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * foreground ctx.rhs -
    ctx.alphaCenter * (1 - ctx.alphaCenter) * background ctx.rhs

def closedFormBackgroundNumerator (ctx : LocalContext ι) : ℝ :=
  (ctx.alphaCenter ^ 2 + ctx.totalWeight) * background ctx.rhs -
    ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground ctx.rhs

noncomputable def closedFormSolution (ctx : LocalContext ι) : LocalUnknown :=
  let b := ctx.rhs
  let det := closedFormDenom ctx
  ![
    (((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * foreground b -
      ctx.alphaCenter * (1 - ctx.alphaCenter) * background b) / det,
    ((ctx.alphaCenter ^ 2 + ctx.totalWeight) * background b -
      ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground b) / det
  ]

noncomputable def inverseSolution (ctx : LocalContext ι) : LocalUnknown :=
  (ctx.normalMatrix⁻¹).mulVec ctx.rhs

theorem closedFormDenom_eq_det (ctx : LocalContext ι) :
    closedFormDenom ctx = ctx.normalMatrix.det := by
  simpa [closedFormDenom] using (normalMatrix_det ctx).symm

@[simp] theorem foreground_closedFormSolution (ctx : LocalContext ι) :
    foreground (closedFormSolution ctx) =
      closedFormForegroundNumerator ctx / closedFormDenom ctx := by
  simp [closedFormSolution, closedFormForegroundNumerator, foreground, background]

@[simp] theorem background_closedFormSolution (ctx : LocalContext ι) :
    background (closedFormSolution ctx) =
      closedFormBackgroundNumerator ctx / closedFormDenom ctx := by
  simp [closedFormSolution, closedFormBackgroundNumerator, foreground, background]

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

end FastMLFE2.Theory.Theorems
