import FastMLFE2.Theory.Theorems.ClosedForm

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem normalMatrix_eq_of_alpha_zero (ctx : LocalContext ι) (hα : ctx.alphaCenter = 0) :
    ctx.normalMatrix = ![![ctx.totalWeight, 0], ![0, 1 + ctx.totalWeight]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [LocalContext.normalMatrix, hα]

theorem normalMatrix_eq_of_alpha_one (ctx : LocalContext ι) (hα : ctx.alphaCenter = 1) :
    ctx.normalMatrix = ![![1 + ctx.totalWeight, 0], ![0, ctx.totalWeight]] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [LocalContext.normalMatrix, hα]

theorem rhs_eq_of_alpha_zero (ctx : LocalContext ι) (hα : ctx.alphaCenter = 0) :
    ctx.rhs = mkLocalUnknown ctx.foregroundSum (ctx.imageValue + ctx.backgroundSum) := by
  ext i; fin_cases i <;> simp [LocalContext.rhs, mkLocalUnknown, hα]

theorem rhs_eq_of_alpha_one (ctx : LocalContext ι) (hα : ctx.alphaCenter = 1) :
    ctx.rhs = mkLocalUnknown (ctx.imageValue + ctx.foregroundSum) ctx.backgroundSum := by
  ext i; fin_cases i <;> simp [LocalContext.rhs, mkLocalUnknown, hα]

theorem closedFormDenom_eq_of_alpha_zero (ctx : LocalContext ι) (hα : ctx.alphaCenter = 0) :
    closedFormDenom ctx = ctx.totalWeight * (ctx.totalWeight + 1) := by
  simp [closedFormDenom, hα]

theorem closedFormDenom_eq_of_alpha_one (ctx : LocalContext ι) (hα : ctx.alphaCenter = 1) :
    closedFormDenom ctx = ctx.totalWeight * (ctx.totalWeight + 1) := by
  simp [closedFormDenom, hα]

private theorem totalWeight_add_one_ne_zero (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.totalWeight + 1 ≠ 0 := by linarith [totalWeight_pos ctx]

theorem closedFormSolution_eq_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    closedFormSolution ctx =
      mkLocalUnknown
        (ctx.foregroundSum / ctx.totalWeight)
        ((ctx.imageValue + ctx.backgroundSum) / (1 + ctx.totalWeight)) := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have htw1 : ctx.totalWeight + 1 ≠ 0 := totalWeight_add_one_ne_zero ctx
  have hsum0 : (∑ j, ctx.neighborWeight j) ≠ 0 := by
    simpa [LocalContext.totalWeight] using htw0
  have hsum1 : (∑ j, ctx.neighborWeight j) + 1 ≠ 0 := by
    simpa [LocalContext.totalWeight] using htw1
  ext i
  fin_cases i
  · suffices
      ((1 + ∑ j, ctx.neighborWeight j) *
          ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j) /
          ((∑ j, ctx.neighborWeight j) * (∑ j, ctx.neighborWeight j + 1)) =
        (∑ j, ctx.neighborWeight j * ctx.fgNeighbor j) / ∑ j, ctx.neighborWeight j by
      simpa [
        closedFormSolution, foreground, background, mkLocalUnknown, hα,
        closedFormDenom_eq_of_alpha_zero,
        rhs_eq_of_alpha_zero ctx hα,
        Fin.zero_eta, Fin.isValue,
        LocalContext.foregroundSum_eq_sum_neighborWeight_mul,
        LocalContext.totalWeight_eq_sum_neighborWeight,
        LocalContext.backgroundSum_eq_sum_neighborWeight_mul
      ]
    field_simp [hsum0, hsum1]; ring
  · suffices
      (∑ j, ctx.neighborWeight j) *
          (ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j) /
          ((∑ j, ctx.neighborWeight j) * (∑ j, ctx.neighborWeight j + 1)) =
        (ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j) /
          (1 + ∑ j, ctx.neighborWeight j) by
      simpa [
        closedFormSolution, foreground, background, mkLocalUnknown, hα,
        closedFormDenom_eq_of_alpha_zero,
        rhs_eq_of_alpha_zero ctx hα,
        Fin.mk_one, Fin.isValue,
        LocalContext.foregroundSum_eq_sum_neighborWeight_mul,
        LocalContext.totalWeight_eq_sum_neighborWeight,
        LocalContext.backgroundSum_eq_sum_neighborWeight_mul
      ]
    field_simp [hsum0, hsum1]
    have hs1' : 1 + ∑ j, ctx.neighborWeight j ≠ 0 := by
      rwa [add_comm] at hsum1
    have hmul :
        ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j =
          (ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j) * 1 :=
      (mul_one _).symm
    conv_lhs =>
      rw [hmul, ← div_self hs1']
    ring

theorem closedFormSolution_eq_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 1) :
    closedFormSolution ctx =
      mkLocalUnknown
        ((ctx.imageValue + ctx.foregroundSum) / (1 + ctx.totalWeight))
        (ctx.backgroundSum / ctx.totalWeight) := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  have htw1 : ctx.totalWeight + 1 ≠ 0 := totalWeight_add_one_ne_zero ctx
  have hsum0 : (∑ j, ctx.neighborWeight j) ≠ 0 := by
    simpa [LocalContext.totalWeight] using htw0
  have hsum1 : (∑ j, ctx.neighborWeight j) + 1 ≠ 0 := by
    simpa [LocalContext.totalWeight] using htw1
  ext i
  fin_cases i
  · suffices
      (∑ j, ctx.neighborWeight j) *
          (ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j) /
          ((∑ j, ctx.neighborWeight j) * (∑ j, ctx.neighborWeight j + 1)) =
        (ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j) /
          (1 + ∑ j, ctx.neighborWeight j) by
      simpa [
        closedFormSolution, foreground, background, mkLocalUnknown, hα,
        closedFormDenom_eq_of_alpha_one,
        rhs_eq_of_alpha_one ctx hα,
        Fin.zero_eta, Fin.isValue,
        LocalContext.foregroundSum_eq_sum_neighborWeight_mul,
        LocalContext.totalWeight_eq_sum_neighborWeight,
        LocalContext.backgroundSum_eq_sum_neighborWeight_mul
      ]
    field_simp [hsum0, hsum1]
    have hs1' : 1 + ∑ j, ctx.neighborWeight j ≠ 0 := by
      rwa [add_comm] at hsum1
    have hmul :
        ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j =
          (ctx.imageValue + ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j) * 1 :=
      (mul_one _).symm
    conv_lhs =>
      rw [hmul, ← div_self hs1']
    ring
  · suffices
      ((1 + ∑ j, ctx.neighborWeight j) *
          ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j) /
          ((∑ j, ctx.neighborWeight j) * (∑ j, ctx.neighborWeight j + 1)) =
        (∑ j, ctx.neighborWeight j * ctx.bgNeighbor j) / ∑ j, ctx.neighborWeight j by
      simpa [
        closedFormSolution, foreground, background, mkLocalUnknown, hα,
        closedFormDenom_eq_of_alpha_one,
        rhs_eq_of_alpha_one ctx hα,
        Fin.mk_one, Fin.isValue,
        LocalContext.foregroundSum_eq_sum_neighborWeight_mul,
        LocalContext.totalWeight_eq_sum_neighborWeight,
        LocalContext.backgroundSum_eq_sum_neighborWeight_mul
      ]
    field_simp [hsum0, hsum1]; ring

example (ctx : LocalContext ι) (hα : ctx.alphaCenter = 0) :
    ctx.normalMatrix = ![![ctx.totalWeight, 0], ![0, 1 + ctx.totalWeight]] :=
  normalMatrix_eq_of_alpha_zero ctx hα

example (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    closedFormSolution ctx =
      mkLocalUnknown
        (ctx.foregroundSum / ctx.totalWeight)
        ((ctx.imageValue + ctx.backgroundSum) / (1 + ctx.totalWeight)) :=
  closedFormSolution_eq_of_alpha_zero ctx hα

example (ctx : LocalContext ι) (hα : ctx.alphaCenter = 1) :
    ctx.rhs = mkLocalUnknown (ctx.imageValue + ctx.foregroundSum) ctx.backgroundSum :=
  rhs_eq_of_alpha_one ctx hα

end LocalContext

end FastMLFE2.Theory.Theorems
