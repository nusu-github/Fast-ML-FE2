import FastMLFE2.Theorems.Solvability.AnchoredInvertibility

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace AnchoredLocalContext

variable {ι : Type*} [Fintype ι]

private theorem solve2x2_foreground
    {a00 a01 a11 b0 b1 det : ℝ}
    (hdet : det = a00 * a11 - a01 * a01) (hdet0 : det ≠ 0) :
    a00 * ((a11 * b0 - a01 * b1) / det) +
        a01 * ((a00 * b1 - a01 * b0) / det) = b0 := by
  field_simp [hdet0]
  rw [hdet]
  ring

private theorem solve2x2_background
    {a00 a01 a11 b0 b1 det : ℝ}
    (hdet : det = a00 * a11 - a01 * a01) (hdet0 : det ≠ 0) :
    a01 * ((a11 * b0 - a01 * b1) / det) +
        a11 * ((a00 * b1 - a01 * b0) / det) = b1 := by
  field_simp [hdet0]
  rw [hdet]
  ring

theorem closedForm_foreground_solves (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight) :
    ctx.normalMatrix.mulVec (ctx.closedFormSolution) 0 = ctx.rhs 0 := by
  simpa [AnchoredLocalContext.closedFormSolution, foreground, background] using
    solve2x2_foreground
      (by
        simp [AnchoredLocalContext.closedFormDenom]
        ring)
      (AnchoredLocalContext.closedFormDenom_ne_zero ctx hfg hbg)

theorem closedForm_background_solves (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight) :
    ctx.normalMatrix.mulVec (ctx.closedFormSolution) 1 = ctx.rhs 1 := by
  simpa [AnchoredLocalContext.closedFormSolution, foreground, background] using
    solve2x2_background
      (by
        simp [AnchoredLocalContext.closedFormDenom]
        ring)
      (AnchoredLocalContext.closedFormDenom_ne_zero ctx hfg hbg)

theorem closedForm_solvesNormalEquation (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight) :
    ctx.SolvesNormalEquation (ctx.closedFormSolution) := by
  funext i
  fin_cases i
  · exact closedForm_foreground_solves ctx hfg hbg
  · exact closedForm_background_solves ctx hfg hbg

private theorem totalWeight_add_anchor_ne_zero (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) :
    ctx.totalWeight + ctx.fgAnchorWeight ≠ 0 := by
  linarith [AnchoredLocalContext.totalWeight_pos ctx]

private theorem totalWeight_add_one_add_anchor_ne_zero (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hbg : 0 ≤ ctx.bgAnchorWeight) :
    1 + ctx.totalWeight + ctx.bgAnchorWeight ≠ 0 := by
  linarith [AnchoredLocalContext.totalWeight_pos ctx]

theorem closedFormSolution_eq_of_alpha_zero
    (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight)
    (hα : ctx.alphaCenter = 0) :
    ctx.closedFormSolution =
      mkLocalUnknown
        ((ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior) / (ctx.totalWeight + ctx.fgAnchorWeight))
        ((ctx.imageValue + ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior) /
          (1 + ctx.totalWeight + ctx.bgAnchorWeight)) := by
  have htwf : ctx.totalWeight + ctx.fgAnchorWeight ≠ 0 :=
    totalWeight_add_anchor_ne_zero ctx hfg
  have htwb : 1 + ctx.totalWeight + ctx.bgAnchorWeight ≠ 0 :=
    totalWeight_add_one_add_anchor_ne_zero ctx hbg
  ext i
  fin_cases i
  · have : foreground (ctx.closedFormSolution) =
        (ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior) /
          (ctx.totalWeight + ctx.fgAnchorWeight) := by
      have hsolve := closedForm_foreground_solves ctx hfg hbg
      rw [AnchoredLocalContext.normalMatrix_mulVec_foreground,
        show ctx.rhs 0 = foreground ctx.rhs from rfl, AnchoredLocalContext.foreground_rhs, hα] at hsolve
      field_simp [htwf]
      linarith
    simpa [mkLocalUnknown] using this
  · have : background (ctx.closedFormSolution) =
        (ctx.imageValue + ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior) /
          (1 + ctx.totalWeight + ctx.bgAnchorWeight) := by
      have hsolve := closedForm_background_solves ctx hfg hbg
      rw [AnchoredLocalContext.normalMatrix_mulVec_background,
        show ctx.rhs 1 = background ctx.rhs from rfl, AnchoredLocalContext.background_rhs, hα] at hsolve
      field_simp [htwb]
      linarith
    simpa [mkLocalUnknown] using this

theorem closedFormSolution_eq_of_alpha_one
    (ctx : AnchoredLocalContext ι)
    [CoreMathAssumptions ctx.toLocalContext]
    (hfg : 0 ≤ ctx.fgAnchorWeight) (hbg : 0 ≤ ctx.bgAnchorWeight)
    (hα : ctx.alphaCenter = 1) :
    ctx.closedFormSolution =
      mkLocalUnknown
        ((ctx.imageValue + ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior) /
          (1 + ctx.totalWeight + ctx.fgAnchorWeight))
        ((ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior) / (ctx.totalWeight + ctx.bgAnchorWeight)) := by
  have htwf : 1 + ctx.totalWeight + ctx.fgAnchorWeight ≠ 0 := by
    linarith [AnchoredLocalContext.totalWeight_pos ctx]
  have htwb : ctx.totalWeight + ctx.bgAnchorWeight ≠ 0 := by
    linarith [AnchoredLocalContext.totalWeight_pos ctx]
  ext i
  fin_cases i
  · have : foreground (ctx.closedFormSolution) =
        (ctx.imageValue + ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior) /
          (1 + ctx.totalWeight + ctx.fgAnchorWeight) := by
      have hsolve := closedForm_foreground_solves ctx hfg hbg
      rw [AnchoredLocalContext.normalMatrix_mulVec_foreground,
        show ctx.rhs 0 = foreground ctx.rhs from rfl, AnchoredLocalContext.foreground_rhs, hα] at hsolve
      field_simp [htwf]
      linarith
    simpa [mkLocalUnknown] using this
  · have : background (ctx.closedFormSolution) =
        (ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior) /
          (ctx.totalWeight + ctx.bgAnchorWeight) := by
      have hsolve := closedForm_background_solves ctx hfg hbg
      rw [AnchoredLocalContext.normalMatrix_mulVec_background,
        show ctx.rhs 1 = background ctx.rhs from rfl, AnchoredLocalContext.background_rhs, hα] at hsolve
      field_simp [htwb]
      linarith
    simpa [mkLocalUnknown] using this

end AnchoredLocalContext

end FastMLFE2.Theorems
