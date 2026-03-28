import Mathlib

namespace FastMLFE2.Theorems

section Relaxation

variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]

/-- Relaxed fixed-point update `x ↦ x + r (J x - x)`. -/
def relaxedUpdate (r : ℝ) (J : α → α) : α → α :=
  fun x => x + r • (J x - x)

/-- Upper bound on the relaxed-update contraction rate. -/
def relaxationContractionRate (r q : ℝ) : ℝ :=
  |1 - r| + r * q

/-- Safe relaxation range `r < λ_max = 2 / (1 + q)` implies a strict contraction rate. -/
noncomputable def relaxationLambdaMax (q : ℝ) : ℝ :=
  2 / (1 + q)

theorem relaxedUpdate_norm_le {J : α → α} {q r : ℝ}
    (hJ : ∀ x y, ‖J x - J y‖ ≤ q * ‖x - y‖)
    (hr : 0 ≤ r)
    (x y : α) :
    ‖relaxedUpdate r J x - relaxedUpdate r J y‖ ≤
      relaxationContractionRate r q * ‖x - y‖ := by
  calc
    ‖relaxedUpdate r J x - relaxedUpdate r J y‖
        = ‖(1 - r) • (x - y) + r • (J x - J y)‖ := by
            simp [relaxedUpdate, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              smul_add, add_smul]
    _ ≤ ‖(1 - r) • (x - y)‖ + ‖r • (J x - J y)‖ := norm_add_le _ _
    _ = |1 - r| * ‖x - y‖ + r * ‖J x - J y‖ := by
          simp [norm_smul, hr]
    _ ≤ |1 - r| * ‖x - y‖ + r * (q * ‖x - y‖) := by
          gcongr
          exact hJ x y
    _ = relaxationContractionRate r q * ‖x - y‖ := by
          dsimp [relaxationContractionRate]
          ring

theorem relaxationContractionRate_lt_one_of_lt_lambdaMax {q r : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 < r) (hrmax : r < relaxationLambdaMax q) :
    relaxationContractionRate r q < 1 := by
  by_cases hrle : r ≤ 1
  · have habs : |1 - r| = 1 - r := abs_of_nonneg (by linarith)
    rw [relaxationContractionRate, habs]
    nlinarith
  · have hrgt : 1 < r := lt_of_not_ge hrle
    have habs : |1 - r| = r - 1 := by
      have hnonpos : 1 - r ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith
    rw [relaxationContractionRate, habs]
    have hden : 0 < 1 + q := by linarith
    have hmul : r * (1 + q) < 2 := by
      exact (lt_div_iff₀ hden).mp hrmax
    nlinarith

theorem relaxedUpdate_contractive_of_lt_lambdaMax {J : α → α} {q r : ℝ}
    (hJ : ∀ x y, ‖J x - J y‖ ≤ q * ‖x - y‖)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 < r) (hrmax : r < relaxationLambdaMax q) :
    relaxationContractionRate r q < 1 ∧
      ∀ x y, ‖relaxedUpdate r J x - relaxedUpdate r J y‖ ≤
        relaxationContractionRate r q * ‖x - y‖ := by
  refine ⟨relaxationContractionRate_lt_one_of_lt_lambdaMax hq0 hq1 hr0 hrmax, ?_⟩
  exact relaxedUpdate_norm_le hJ hr0.le

end Relaxation

section IterationBudget

theorem scale_mul_pow_le_of_log_threshold
    {scale eta rho : ℝ}
    {k : Nat}
    (hscale : 0 < scale)
    (heta : 0 < eta)
    (hrho0 : 0 < rho)
    (hrho1 : rho < 1)
    (hk : 1 + Real.log (scale / eta) / Real.log (1 / rho) ≤ (k + 1 : ℝ)) :
    scale * rho ^ k ≤ eta := by
  have hlogDenPos : 0 < Real.log (1 / rho) := Real.log_pos (one_lt_one_div hrho0 hrho1)
  have hk' : Real.log (scale / eta) ≤ (k : ℝ) * Real.log (1 / rho) :=
    (div_le_iff₀ hlogDenPos).1 (by nlinarith)
  have hdivle' : scale / eta ≤ (1 / rho : ℝ) ^ k := by
    have hposR := Real.rpow_pos_of_pos (one_div_pos.mpr hrho0) (k : ℝ)
    have := (Real.strictMonoOn_log.le_iff_le (div_pos hscale heta) hposR).1
      (by rw [Real.log_rpow (one_div_pos.mpr hrho0)]; exact hk')
    simpa [Real.rpow_natCast] using this
  have hunit : ((1 / rho : ℝ) ^ k) * rho ^ k = 1 := by
    rw [one_div_pow]
    field_simp [pow_ne_zero k hrho0.ne']
  have hscalele : scale ≤ eta * ((1 / rho : ℝ) ^ k) := by
    linarith [(div_le_iff₀ heta).1 hdivle']
  calc
    scale * rho ^ k ≤ (eta * ((1 / rho : ℝ) ^ k)) * rho ^ k :=
        mul_le_mul_of_nonneg_right hscalele (pow_pos hrho0 _).le
    _ = eta := by
      rw [mul_assoc, hunit, mul_one]

theorem error_le_of_log_threshold
    {error scale eta rho : ℝ}
    {k : Nat}
    (herror : error ≤ scale * rho ^ k)
    (hscale : 0 < scale)
    (heta : 0 < eta)
    (hrho0 : 0 < rho)
    (hrho1 : rho < 1)
    (hk : 1 + Real.log (scale / eta) / Real.log (1 / rho) ≤ (k + 1 : ℝ)) :
    error ≤ eta :=
  herror.trans (scale_mul_pow_le_of_log_threshold hscale heta hrho0 hrho1 hk)

end IterationBudget

section Sharpness

def signFlipContraction (q : ℝ) : ℝ → ℝ :=
  fun x => -q * x

def signFlipRelaxed (r q : ℝ) : ℝ → ℝ :=
  fun x => x + r * (signFlipContraction q x - x)

theorem signFlipContraction_dist
    (hq0 : 0 ≤ q) (x y : ℝ) :
    ‖signFlipContraction q x - signFlipContraction q y‖ = q * ‖x - y‖ := by
  have h1 : signFlipContraction q x - signFlipContraction q y = q * (y - x) := by
    simp [signFlipContraction]
    ring
  rw [h1]
  simp [norm_mul, hq0, abs_sub_comm]

theorem signFlipRelaxed_one_zero_eq
    (r q : ℝ) :
    signFlipRelaxed r q 1 - signFlipRelaxed r q 0 = 1 - r * (1 + q) := by
  simp [signFlipRelaxed, signFlipContraction]
  ring

theorem signFlipRelaxed_one_zero_dist_gt_one_of_gt_lambdaMax
    (hq0 : 0 ≤ q)
    (hrgt : relaxationLambdaMax q < r) :
    1 < ‖signFlipRelaxed r q 1 - signFlipRelaxed r q 0‖ := by
  have hden : 0 < 1 + q := by
    dsimp [relaxationLambdaMax] at hrgt
    linarith
  have hmul : 2 < r * (1 + q) := by
    have htmp : 2 < (1 + q) * r := by
      exact (div_lt_iff₀' hden).mp hrgt
    simpa [mul_comm, mul_left_comm, mul_assoc, relaxationLambdaMax] using htmp
  have hneg : 1 - r * (1 + q) < 0 := by
    linarith
  have habs : ‖signFlipRelaxed r q 1 - signFlipRelaxed r q 0‖ = r * (1 + q) - 1 := by
    rw [signFlipRelaxed_one_zero_eq]
    simp [abs_of_neg hneg]
  rw [habs]
  nlinarith

end Sharpness

end FastMLFE2.Theorems
