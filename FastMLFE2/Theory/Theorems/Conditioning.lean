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
  ext i j; fin_cases i <;> fin_cases j <;> simp [LocalContext.normalMatrix, add_comm]

omit [Fintype ι] in
theorem alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one
    (ctx : LocalContext ι) :
    alphaQuadratic ctx = 2 * ctx.alphaCenter ^ 2 - 2 * ctx.alphaCenter + 1 := by
  simp [alphaQuadratic]; ring

theorem one_half_le_alphaQuadratic
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    (1 : ℝ) / 2 ≤ alphaQuadratic ctx := by
  nlinarith [alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one ctx,
    sq_nonneg (ctx.alphaCenter - (1 : ℝ) / 2)]

theorem alphaQuadratic_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    alphaQuadratic ctx ≤ 1 := by
  nlinarith [alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one ctx,
    CoreMathAssumptions.alphaCenterBounded (ctx := ctx)]

omit [Fintype ι] in
theorem alphaQuadratic_eq_one_of_alpha_zero
    (ctx : LocalContext ι) (hα : ctx.alphaCenter = 0) :
    alphaQuadratic ctx = 1 := by simp [alphaQuadratic, hα]

omit [Fintype ι] in
theorem alphaQuadratic_eq_one_of_alpha_one
    (ctx : LocalContext ι) (hα : ctx.alphaCenter = 1) :
    alphaQuadratic ctx = 1 := by simp [alphaQuadratic, hα]

omit [Fintype ι] in
theorem alphaQuadratic_eq_one_half_of_alpha_half
    (ctx : LocalContext ι) (hα : ctx.alphaCenter = (1 : ℝ) / 2) :
    alphaQuadratic ctx = (1 : ℝ) / 2 := by
  unfold alphaQuadratic; rw [hα]; norm_num

theorem normalMatrix_mulVec_uVec
    (ctx : LocalContext ι) :
    ctx.normalMatrix.mulVec (uVec ctx.alphaCenter) =
      fun i => (ctx.totalWeight + alphaQuadratic ctx) * uVec ctx.alphaCenter i := by
  ext i; fin_cases i <;>
    simp [alphaQuadratic, uVec, foreground, background,
      LocalContext.normalMatrix_mulVec_foreground, LocalContext.normalMatrix_mulVec_background] <;>
    ring_nf

theorem normalMatrix_mulVec_orthVec
    (ctx : LocalContext ι) :
    ctx.normalMatrix.mulVec (orthVec ctx) =
      fun i => ctx.totalWeight * orthVec ctx i := by
  ext i; fin_cases i <;>
    simp [orthVec, foreground, background,
      LocalContext.normalMatrix_mulVec_foreground, LocalContext.normalMatrix_mulVec_background] <;>
    ring_nf

omit [Fintype ι] in
theorem uVec_ne_zero (ctx : LocalContext ι) : uVec ctx.alphaCenter ≠ 0 := by
  intro h
  have hfg := congrArg foreground h; have hbg := congrArg background h
  simp [foreground, background, uVec] at hfg hbg; nlinarith

omit [Fintype ι] in
theorem orthVec_ne_zero (ctx : LocalContext ι) : orthVec ctx ≠ 0 := by
  intro h
  have hfg := congrArg foreground h; have hbg := congrArg background h
  simp [foreground, background, orthVec] at hfg hbg; nlinarith

theorem totalWeight_is_local_eigenvalue (ctx : LocalContext ι) :
    ∃ v : LocalUnknown, v ≠ 0 ∧
      ctx.normalMatrix.mulVec v = fun i => ctx.totalWeight * v i :=
  ⟨_, orthVec_ne_zero ctx, normalMatrix_mulVec_orthVec ctx⟩

theorem totalWeight_add_alphaQuadratic_is_local_eigenvalue (ctx : LocalContext ι) :
    ∃ v : LocalUnknown, v ≠ 0 ∧
      ctx.normalMatrix.mulVec v = fun i => (ctx.totalWeight + alphaQuadratic ctx) * v i :=
  ⟨_, uVec_ne_zero ctx, normalMatrix_mulVec_uVec ctx⟩

noncomputable def localConditionNumber (ctx : LocalContext ι) : ℝ :=
  (ctx.totalWeight + alphaQuadratic ctx) / ctx.totalWeight

theorem localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    localConditionNumber ctx = 1 + alphaQuadratic ctx / ctx.totalWeight := by
  rw [localConditionNumber]; field_simp [(totalWeight_pos ctx).ne']

theorem localConditionNumber_lower_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    1 + ((1 : ℝ) / 2) / ctx.totalWeight ≤ localConditionNumber ctx := by
  rw [localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight]
  gcongr
  · exact (totalWeight_pos ctx).le
  · exact one_half_le_alphaQuadratic ctx

theorem localConditionNumber_upper_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    localConditionNumber ctx ≤ 1 + 1 / ctx.totalWeight := by
  rw [localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight]
  gcongr
  · exact (totalWeight_pos ctx).le
  · exact alphaQuadratic_le_one ctx

theorem localConditionNumber_eq_best_case_of_alpha_half
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = (1 : ℝ) / 2) :
    localConditionNumber ctx = 1 + ((1 : ℝ) / 2) / ctx.totalWeight := by
  rw [localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight,
    alphaQuadratic_eq_one_half_of_alpha_half ctx hα]

theorem localConditionNumber_eq_worst_case_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    localConditionNumber ctx = 1 + 1 / ctx.totalWeight := by
  rw [localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight,
    alphaQuadratic_eq_one_of_alpha_zero ctx hα]

theorem localConditionNumber_eq_worst_case_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 1) :
    localConditionNumber ctx = 1 + 1 / ctx.totalWeight := by
  rw [localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight,
    alphaQuadratic_eq_one_of_alpha_one ctx hα]

theorem localConditionNumber_bounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    1 + ((1 : ℝ) / 2) / ctx.totalWeight ≤ localConditionNumber ctx ∧
      localConditionNumber ctx ≤ 1 + 1 / ctx.totalWeight :=
  ⟨localConditionNumber_lower_bound ctx, localConditionNumber_upper_bound ctx⟩

end LocalContext

end FastMLFE2.Theory.Theorems
