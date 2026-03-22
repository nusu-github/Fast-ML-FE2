import FastMLFE2.Theory.Theorems.Invertibility

namespace FastMLFE2.Theory.Theorems

/-!
H12 local conditioning structure for the single-pixel normal matrix.
-/

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

private def alphaQuadratic (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2

private def orthVec (ctx : LocalContext ι) : LocalUnknown :=
  ![1 - ctx.alphaCenter, -ctx.alphaCenter]

theorem normalMatrix_eq_totalWeight_plus_uOuter
    (ctx : LocalContext ι) :
    ctx.normalMatrix =
      ![![ctx.totalWeight + ctx.alphaCenter ^ 2,
          ctx.alphaCenter * (1 - ctx.alphaCenter)],
        ![ctx.alphaCenter * (1 - ctx.alphaCenter),
          ctx.totalWeight + (1 - ctx.alphaCenter) ^ 2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LocalContext.normalMatrix, add_comm]

omit [Fintype ι] in
theorem alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one
    (ctx : LocalContext ι) :
    alphaQuadratic ctx =
      2 * ctx.alphaCenter ^ 2 - 2 * ctx.alphaCenter + 1 := by
  simp [alphaQuadratic]
  ring

theorem one_half_le_alphaQuadratic
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    (1 : ℝ) / 2 ≤ alphaQuadratic ctx := by
  have hpoly := alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one ctx
  have hsquare : 0 ≤ (ctx.alphaCenter - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
  nlinarith

theorem alphaQuadratic_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    alphaQuadratic ctx ≤ 1 := by
  have hpoly := alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one ctx
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  nlinarith

omit [Fintype ι] in
theorem alphaQuadratic_eq_one_of_alpha_zero
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 0) :
    alphaQuadratic ctx = 1 := by
  simp [alphaQuadratic, hα]

omit [Fintype ι] in
theorem alphaQuadratic_eq_one_of_alpha_one
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 1) :
    alphaQuadratic ctx = 1 := by
  simp [alphaQuadratic, hα]

omit [Fintype ι] in
theorem alphaQuadratic_eq_one_half_of_alpha_half
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = (1 : ℝ) / 2) :
    alphaQuadratic ctx = (1 : ℝ) / 2 := by
  unfold alphaQuadratic
  rw [hα]
  norm_num

end LocalContext

end FastMLFE2.Theory.Theorems
