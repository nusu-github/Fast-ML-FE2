import FastMLFE2.Theory.Core.LocalSemantics
import FastMLFE2.Theory.Theorems.Invertibility

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
    (hdet : det = a00 * a11 - a01 * a01)
    (hdet0 : det ≠ 0) :
    a00 * ((a11 * b0 - a01 * b1) / det) +
        a01 * ((a00 * b1 - a01 * b0) / det) = b0 := by
  field_simp [hdet0]
  rw [hdet]
  ring

private theorem solve2x2_background
    {a00 a01 a11 b0 b1 det : ℝ}
    (hdet : det = a00 * a11 - a01 * a01)
    (hdet0 : det ≠ 0) :
    a01 * ((a11 * b0 - a01 * b1) / det) +
        a11 * ((a00 * b1 - a01 * b0) / det) = b1 := by
  field_simp [hdet0]
  rw [hdet]
  ring

def closedFormDenom (ctx : LocalContext ι) : ℝ :=
  ctx.totalWeight * (ctx.totalWeight + ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)

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

theorem closedFormDenom_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < closedFormDenom ctx := by
  rw [closedFormDenom_eq_det]
  exact normalMatrix_det_pos ctx

theorem inverseSolution_solvesNormalEquation (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.SolvesNormalEquation (inverseSolution ctx) := by
  have hunit : IsUnit ctx.normalMatrix.det := normalMatrix_det_isUnit ctx
  dsimp [FastMLFE2.Theory.Core.LocalContext.SolvesNormalEquation, inverseSolution]
  rw [Matrix.mulVec_mulVec]
  simpa [Matrix.one_mulVec] using
    congrArg (fun M : Matrix LocalIdx LocalIdx ℝ => M.mulVec ctx.rhs)
      (Matrix.mul_nonsing_inv ctx.normalMatrix hunit)

private theorem closedFormDenom_eq_minor (ctx : LocalContext ι) :
    closedFormDenom ctx =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight) * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) -
        (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 := by
  simp [closedFormDenom]
  ring

theorem closedForm_foreground_solves (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.mulVec (closedFormSolution ctx) 0 = ctx.rhs 0 := by
  have hdet0 : closedFormDenom ctx ≠ 0 := (closedFormDenom_pos ctx).ne'
  simpa [closedFormSolution, foreground, background]
    using
      solve2x2_foreground
        (a00 := ctx.alphaCenter ^ 2 + ctx.totalWeight)
        (a01 := ctx.alphaCenter * (1 - ctx.alphaCenter))
        (a11 := (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight)
        (b0 := ctx.rhs 0)
        (b1 := ctx.rhs 1)
        (det := closedFormDenom ctx)
        (by simpa [pow_two] using closedFormDenom_eq_minor ctx)
        hdet0

theorem closedForm_background_solves (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.mulVec (closedFormSolution ctx) 1 = ctx.rhs 1 := by
  have hdet0 : closedFormDenom ctx ≠ 0 := (closedFormDenom_pos ctx).ne'
  simpa [closedFormSolution, foreground, background]
    using
      solve2x2_background
        (a00 := ctx.alphaCenter ^ 2 + ctx.totalWeight)
        (a01 := ctx.alphaCenter * (1 - ctx.alphaCenter))
        (a11 := (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight)
        (b0 := ctx.rhs 0)
        (b1 := ctx.rhs 1)
        (det := closedFormDenom ctx)
        (by simpa [pow_two] using closedFormDenom_eq_minor ctx)
        hdet0

theorem eq_inverseSolution_of_solves (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    {g : LocalUnknown}
    (hg : ctx.SolvesNormalEquation g) :
    g = inverseSolution ctx := by
  have hunit : IsUnit ctx.normalMatrix.det := normalMatrix_det_isUnit ctx
  have hleft :
      (ctx.normalMatrix⁻¹ * ctx.normalMatrix).mulVec g = inverseSolution ctx := by
    simpa [inverseSolution,
      FastMLFE2.Theory.Core.LocalContext.SolvesNormalEquation,
      Matrix.mulVec_mulVec] using
      congrArg (fun v => ctx.normalMatrix⁻¹.mulVec v) hg
  have hone :
      (ctx.normalMatrix⁻¹ * ctx.normalMatrix).mulVec g =
        (1 : Matrix LocalIdx LocalIdx ℝ).mulVec g := by
    simpa [Matrix.one_mulVec] using
      congrArg (fun M : Matrix LocalIdx LocalIdx ℝ => M.mulVec g)
        (Matrix.nonsing_inv_mul ctx.normalMatrix hunit)
  have hvec : (1 : Matrix LocalIdx LocalIdx ℝ).mulVec g = inverseSolution ctx := by
    exact hone.symm.trans hleft
  simpa [Matrix.one_mulVec] using hvec

theorem closedForm_solvesNormalEquation (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.SolvesNormalEquation (closedFormSolution ctx) := by
  funext i
  fin_cases i
  · exact closedForm_foreground_solves ctx
  · exact closedForm_background_solves ctx

theorem closedForm_eq_inverseSolution (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    closedFormSolution ctx = inverseSolution ctx := by
  exact eq_inverseSolution_of_solves ctx (closedForm_solvesNormalEquation ctx)

end LocalContext

end FastMLFE2.Theory.Theorems
