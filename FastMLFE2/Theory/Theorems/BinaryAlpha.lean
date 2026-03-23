import FastMLFE2.Theory.Theorems.ClosedForm

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem normalMatrix_eq_of_alpha_zero
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 0) :
    ctx.normalMatrix =
      ![![ctx.totalWeight, 0],
        ![0, 1 + ctx.totalWeight]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [FastMLFE2.Theory.Core.LocalContext.normalMatrix, hα]

theorem normalMatrix_eq_of_alpha_one
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 1) :
    ctx.normalMatrix =
      ![![1 + ctx.totalWeight, 0],
        ![0, ctx.totalWeight]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [FastMLFE2.Theory.Core.LocalContext.normalMatrix, hα]

theorem rhs_eq_of_alpha_zero
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 0) :
    ctx.rhs =
      mkLocalUnknown
        ctx.foregroundSum
        (ctx.imageValue + ctx.backgroundSum) := by
  ext i
  fin_cases i
  · simp [FastMLFE2.Theory.Core.LocalContext.rhs, mkLocalUnknown, hα]
  · simp [FastMLFE2.Theory.Core.LocalContext.rhs, mkLocalUnknown, hα]

theorem rhs_eq_of_alpha_one
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 1) :
    ctx.rhs =
      mkLocalUnknown
        (ctx.imageValue + ctx.foregroundSum)
        ctx.backgroundSum := by
  ext i
  fin_cases i
  · simp [FastMLFE2.Theory.Core.LocalContext.rhs, mkLocalUnknown, hα]
  · simp [FastMLFE2.Theory.Core.LocalContext.rhs, mkLocalUnknown, hα]

theorem closedFormDenom_eq_of_alpha_zero
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 0) :
    closedFormDenom ctx = ctx.totalWeight * (ctx.totalWeight + 1) := by
  simp [closedFormDenom, hα]

theorem closedFormDenom_eq_of_alpha_one
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 1) :
    closedFormDenom ctx = ctx.totalWeight * (ctx.totalWeight + 1) := by
  simp [closedFormDenom, hα]

private theorem totalWeight_add_one_ne_zero
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    ctx.totalWeight + 1 ≠ 0 := by
  have htw : 0 < ctx.totalWeight := totalWeight_pos ctx
  linarith

theorem closedFormSolution_eq_of_alpha_zero
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 0) :
    closedFormSolution ctx =
      mkLocalUnknown
        (ctx.foregroundSum / ctx.totalWeight)
        ((ctx.imageValue + ctx.backgroundSum) / (1 + ctx.totalWeight)) := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have htw1 : ctx.totalWeight + 1 ≠ 0 := totalWeight_add_one_ne_zero ctx
  have hsum0 : (∑ j, ctx.neighborWeight j) ≠ 0 := by
    simpa [FastMLFE2.Theory.Core.LocalContext.totalWeight] using htw0
  have hsum1 : (∑ j, ctx.neighborWeight j) + 1 ≠ 0 := by
    simpa [FastMLFE2.Theory.Core.LocalContext.totalWeight] using htw1
  ext i
  fin_cases i
  · simp [closedFormSolution, foreground, background, mkLocalUnknown, hα,
      closedFormDenom_eq_of_alpha_zero, rhs_eq_of_alpha_zero (ctx := ctx) hα]
    set s : ℝ := ∑ j, ctx.neighborWeight j
    have hs0 : s ≠ 0 := by simpa [s] using hsum0
    have hs1 : s + 1 ≠ 0 := by simpa [s] using hsum1
    field_simp [hs0, hs1]
    ring
  · simp [closedFormSolution, foreground, background, mkLocalUnknown, hα,
      closedFormDenom_eq_of_alpha_zero, rhs_eq_of_alpha_zero (ctx := ctx) hα]
    set s : ℝ := ∑ j, ctx.neighborWeight j
    set t : ℝ := ctx.imageValue + ∑ x, ctx.neighborWeight x * ctx.bgNeighbor x
    have hs0 : s ≠ 0 := by simpa [s] using hsum0
    have hs1 : s + 1 ≠ 0 := by simpa [s] using hsum1
    field_simp [hs0, hs1]
    have hs1' : 1 + s ≠ 0 := by simpa [add_comm] using hs1
    have hdiv : (s + 1) / (1 + s) = (1 : ℝ) := by
      simpa [add_comm] using (div_self hs1')
    have hmul := congrArg (fun x : ℝ => t * x) hdiv.symm
    simpa [div_eq_mul_inv, add_mul, mul_add, mul_assoc, t] using hmul

theorem closedFormSolution_eq_of_alpha_one
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 1) :
    closedFormSolution ctx =
      mkLocalUnknown
        ((ctx.imageValue + ctx.foregroundSum) / (1 + ctx.totalWeight))
        (ctx.backgroundSum / ctx.totalWeight) := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have htw1 : ctx.totalWeight + 1 ≠ 0 := totalWeight_add_one_ne_zero ctx
  have hsum0 : (∑ j, ctx.neighborWeight j) ≠ 0 := by
    simpa [FastMLFE2.Theory.Core.LocalContext.totalWeight] using htw0
  have hsum1 : (∑ j, ctx.neighborWeight j) + 1 ≠ 0 := by
    simpa [FastMLFE2.Theory.Core.LocalContext.totalWeight] using htw1
  ext i
  fin_cases i
  · simp [closedFormSolution, foreground, background, mkLocalUnknown, hα,
      closedFormDenom_eq_of_alpha_one, rhs_eq_of_alpha_one (ctx := ctx) hα]
    set s : ℝ := ∑ j, ctx.neighborWeight j
    set t : ℝ := ctx.imageValue + ∑ x, ctx.neighborWeight x * ctx.fgNeighbor x
    have hs0 : s ≠ 0 := by simpa [s] using hsum0
    have hs1 : s + 1 ≠ 0 := by simpa [s] using hsum1
    field_simp [hs0, hs1]
    have hs1' : 1 + s ≠ 0 := by simpa [add_comm] using hs1
    have hdiv : (s + 1) / (1 + s) = (1 : ℝ) := by
      simpa [add_comm] using (div_self hs1')
    have hmul := congrArg (fun x : ℝ => t * x) hdiv.symm
    simpa [div_eq_mul_inv, add_mul, mul_add, mul_assoc, t] using hmul
  · simp [closedFormSolution, foreground, background, mkLocalUnknown, hα,
      closedFormDenom_eq_of_alpha_one, rhs_eq_of_alpha_one (ctx := ctx) hα]
    set s : ℝ := ∑ j, ctx.neighborWeight j
    have hs0 : s ≠ 0 := by simpa [s] using hsum0
    have hs1 : s + 1 ≠ 0 := by simpa [s] using hsum1
    field_simp [hs0, hs1]
    ring

example (ctx : LocalContext ι) (hα : ctx.alphaCenter = 0) :
    ctx.normalMatrix =
      ![![ctx.totalWeight, 0],
        ![0, 1 + ctx.totalWeight]] := by
  simpa using normalMatrix_eq_of_alpha_zero (ctx := ctx) hα

example (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    closedFormSolution ctx =
      mkLocalUnknown
        (ctx.foregroundSum / ctx.totalWeight)
        ((ctx.imageValue + ctx.backgroundSum) / (1 + ctx.totalWeight)) := by
  simpa using closedFormSolution_eq_of_alpha_zero (ctx := ctx) hα

example (ctx : LocalContext ι) (hα : ctx.alphaCenter = 1) :
    ctx.rhs =
      mkLocalUnknown
        (ctx.imageValue + ctx.foregroundSum)
        ctx.backgroundSum := by
  simpa using rhs_eq_of_alpha_one (ctx := ctx) hα

end LocalContext

end FastMLFE2.Theory.Theorems
