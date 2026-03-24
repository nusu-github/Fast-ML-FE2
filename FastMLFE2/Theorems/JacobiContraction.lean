import FastMLFE2.Theorems.Conditioning
import FastMLFE2.Theorems.BinaryAlpha

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def jacobiDiagForeground (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter ^ 2 + ctx.totalWeight

def jacobiDiagBackground (ctx : LocalContext ι) : ℝ :=
  (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight

def jacobiCrossTerm (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter * (1 - ctx.alphaCenter)

noncomputable def jacobiForegroundCoeff (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / jacobiDiagForeground ctx

noncomputable def jacobiBackgroundCoeff (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / jacobiDiagBackground ctx

noncomputable def jacobiStep (ctx : LocalContext ι) (g : LocalUnknown) : LocalUnknown :=
  mkLocalUnknown
    ((foreground ctx.rhs - jacobiCrossTerm ctx * background g) / jacobiDiagForeground ctx)
    ((background ctx.rhs - jacobiCrossTerm ctx * foreground g) / jacobiDiagBackground ctx)

noncomputable def jacobiDifferenceMap (ctx : LocalContext ι) (g : LocalUnknown) : LocalUnknown :=
  mkLocalUnknown
    (-(jacobiForegroundCoeff ctx) * background g)
    (-(jacobiBackgroundCoeff ctx) * foreground g)

def localInfinityNorm (g : LocalUnknown) : ℝ :=
  max |foreground g| |background g|

noncomputable def jacobiSpectralRadiusSq (ctx : LocalContext ι) : ℝ :=
  jacobiForegroundCoeff ctx * jacobiBackgroundCoeff ctx

noncomputable def jacobiSpectralRadius (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / Real.sqrt (jacobiDiagForeground ctx * jacobiDiagBackground ctx)

@[simp] theorem jacobiStep_foreground (ctx : LocalContext ι) (g : LocalUnknown) :
    foreground (jacobiStep ctx g) =
      (foreground ctx.rhs - jacobiCrossTerm ctx * background g) / jacobiDiagForeground ctx := by
  simp [jacobiStep]

@[simp] theorem jacobiStep_background (ctx : LocalContext ι) (g : LocalUnknown) :
    background (jacobiStep ctx g) =
      (background ctx.rhs - jacobiCrossTerm ctx * foreground g) / jacobiDiagBackground ctx := by
  simp [jacobiStep]

@[simp] theorem jacobiDifferenceMap_foreground (ctx : LocalContext ι) (g : LocalUnknown) :
    foreground (jacobiDifferenceMap ctx g) = -(jacobiForegroundCoeff ctx) * background g := by
  simp [jacobiDifferenceMap]

@[simp] theorem jacobiDifferenceMap_background (ctx : LocalContext ι) (g : LocalUnknown) :
    background (jacobiDifferenceMap ctx g) = -(jacobiBackgroundCoeff ctx) * foreground g := by
  simp [jacobiDifferenceMap]

theorem jacobiStep_sub_eq (ctx : LocalContext ι) (x y : LocalUnknown) :
    jacobiStep ctx x - jacobiStep ctx y = jacobiDifferenceMap ctx (x - y) := by
  ext i; fin_cases i <;>
    simp [sub_eq_add_neg, jacobiStep, jacobiDifferenceMap, jacobiForegroundCoeff,
      jacobiBackgroundCoeff, jacobiCrossTerm, jacobiDiagForeground, jacobiDiagBackground,
      foreground, background, mkLocalUnknown] <;> ring_nf

theorem jacobiDifferenceMap_sq_eq (ctx : LocalContext ι) (g : LocalUnknown) :
    jacobiDifferenceMap ctx (jacobiDifferenceMap ctx g) =
      fun i => jacobiSpectralRadiusSq ctx * g i := by
  ext i; fin_cases i <;>
    simp [jacobiDifferenceMap, jacobiSpectralRadiusSq, jacobiForegroundCoeff,
      jacobiBackgroundCoeff, foreground, background, mkLocalUnknown] <;> ring_nf

theorem jacobiDiagForeground_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < jacobiDiagForeground ctx := by
  simpa [jacobiDiagForeground] using
    add_pos_of_nonneg_of_pos (sq_nonneg ctx.alphaCenter) (totalWeight_pos ctx)

theorem jacobiDiagBackground_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < jacobiDiagBackground ctx := by
  simpa [jacobiDiagBackground, add_comm] using
    add_pos_of_nonneg_of_pos (sq_nonneg (1 - ctx.alphaCenter)) (totalWeight_pos ctx)

theorem jacobiCrossTerm_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ jacobiCrossTerm ctx := by
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  simpa [jacobiCrossTerm] using mul_nonneg hα.1 (sub_nonneg.2 hα.2)

theorem jacobiSpectralRadiusSq_eq (ctx : LocalContext ι) :
    jacobiSpectralRadiusSq ctx =
      (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2 /
        ((ctx.alphaCenter ^ 2 + ctx.totalWeight) *
          ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight)) := by
  simp [jacobiSpectralRadiusSq, jacobiForegroundCoeff, jacobiBackgroundCoeff,
    jacobiCrossTerm, jacobiDiagForeground, jacobiDiagBackground]
  ring_nf; field_simp; ring

private theorem sq_div_sqrt {a b : ℝ} (hb : 0 < b) :
    (a / Real.sqrt b) ^ 2 = a ^ 2 / b := by
  field_simp [pow_two, (Real.sqrt_ne_zero hb.le).2 hb.ne']
  rw [Real.sq_sqrt hb.le]

theorem jacobiSpectralRadius_sq (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    jacobiSpectralRadius ctx ^ 2 = jacobiSpectralRadiusSq ctx := by
  rw [jacobiSpectralRadius, jacobiSpectralRadiusSq_eq,
    sq_div_sqrt (mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx))]
  simp [jacobiCrossTerm, jacobiDiagForeground, jacobiDiagBackground]

theorem jacobiSpectralRadius_lt_one (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    jacobiSpectralRadius ctx < 1 := by
  have hnonneg : 0 ≤ jacobiSpectralRadius ctx :=
    div_nonneg (jacobiCrossTerm_nonneg ctx) (Real.sqrt_nonneg _)
  have hsq_lt : jacobiSpectralRadius ctx ^ 2 < 1 := by
    rw [jacobiSpectralRadius_sq, jacobiSpectralRadiusSq_eq]
    have hden : 0 < (ctx.alphaCenter ^ 2 + ctx.totalWeight) *
        ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) :=
      mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)
    rw [div_lt_one hden]
    nlinarith [totalWeight_pos ctx]
  nlinarith

theorem jacobiSpectralRadius_eq_zero_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    jacobiSpectralRadius ctx = 0 := by simp [jacobiSpectralRadius, jacobiCrossTerm, hα]

theorem jacobiSpectralRadius_eq_zero_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 1) :
    jacobiSpectralRadius ctx = 0 := by simp [jacobiSpectralRadius, jacobiCrossTerm, hα]

theorem jacobiTwoStep_sub_eq (ctx : LocalContext ι) (x y : LocalUnknown) :
    jacobiStep ctx (jacobiStep ctx x) - jacobiStep ctx (jacobiStep ctx y) =
      fun i => jacobiSpectralRadiusSq ctx * (x - y) i := by
  rw [jacobiStep_sub_eq, jacobiStep_sub_eq]; exact jacobiDifferenceMap_sq_eq ctx (x - y)

theorem localInfinityNorm_smul_nonneg {c : ℝ} (hc : 0 ≤ c) (g : LocalUnknown) :
    localInfinityNorm (fun i => c * g i) = c * localInfinityNorm g := by
  simp [localInfinityNorm, foreground, background, abs_mul, abs_of_nonneg hc,
    mul_max_of_nonneg, hc]

theorem jacobiTwoStep_infty_contraction
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (x y : LocalUnknown) :
    localInfinityNorm (jacobiStep ctx (jacobiStep ctx x) - jacobiStep ctx (jacobiStep ctx y)) =
      jacobiSpectralRadiusSq ctx * localInfinityNorm (x - y) := by
  rw [jacobiTwoStep_sub_eq]
  have hsq_nonneg : 0 ≤ jacobiSpectralRadiusSq ctx := by
    rw [jacobiSpectralRadiusSq_eq]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)))
  exact localInfinityNorm_smul_nonneg hsq_nonneg (x - y)

noncomputable def jacobiIterate (ctx : LocalContext ι) (k : Nat) : LocalUnknown → LocalUnknown :=
  Nat.iterate (jacobiStep ctx) k

theorem jacobiStep_closedFormSolution (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    jacobiStep ctx (closedFormSolution ctx) = closedFormSolution ctx := by
  ext i; fin_cases i
  · have hdiag0 : jacobiDiagForeground ctx ≠ 0 := (jacobiDiagForeground_pos ctx).ne'
    have hsolve :
        jacobiDiagForeground ctx * foreground (closedFormSolution ctx) +
            jacobiCrossTerm ctx * background (closedFormSolution ctx) =
          foreground ctx.rhs := by
      simpa [jacobiDiagForeground, jacobiCrossTerm] using closedForm_foreground_solves ctx
    have hrhs :
        foreground ctx.rhs - jacobiCrossTerm ctx * background (closedFormSolution ctx) =
          jacobiDiagForeground ctx * foreground (closedFormSolution ctx) := by linarith
    calc foreground (jacobiStep ctx (closedFormSolution ctx)) =
        (jacobiDiagForeground ctx * foreground (closedFormSolution ctx)) /
          jacobiDiagForeground ctx := by rw [jacobiStep_foreground, hrhs]
      _ = foreground (closedFormSolution ctx) := mul_div_cancel_left₀ _ hdiag0
  · have hdiag0 : jacobiDiagBackground ctx ≠ 0 := (jacobiDiagBackground_pos ctx).ne'
    have hsolve :
        jacobiCrossTerm ctx * foreground (closedFormSolution ctx) +
            jacobiDiagBackground ctx * background (closedFormSolution ctx) =
          background ctx.rhs := by
      simpa [jacobiDiagBackground, jacobiCrossTerm] using closedForm_background_solves ctx
    have hrhs :
        background ctx.rhs - jacobiCrossTerm ctx * foreground (closedFormSolution ctx) =
          jacobiDiagBackground ctx * background (closedFormSolution ctx) := by linarith
    calc background (jacobiStep ctx (closedFormSolution ctx)) =
        (jacobiDiagBackground ctx * background (closedFormSolution ctx)) /
          jacobiDiagBackground ctx := by rw [jacobiStep_background, hrhs]
      _ = background (closedFormSolution ctx) := mul_div_cancel_left₀ _ hdiag0

theorem localInfinityNorm_nonneg (g : LocalUnknown) : 0 ≤ localInfinityNorm g :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem foreground_abs_le_localInfinityNorm (g : LocalUnknown) :
    |foreground g| ≤ localInfinityNorm g := le_max_left _ _

theorem background_abs_le_localInfinityNorm (g : LocalUnknown) :
    |background g| ≤ localInfinityNorm g := le_max_right _ _

theorem jacobiForegroundCoeff_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ jacobiForegroundCoeff ctx :=
  div_nonneg (jacobiCrossTerm_nonneg ctx) (jacobiDiagForeground_pos ctx).le

theorem jacobiBackgroundCoeff_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ jacobiBackgroundCoeff ctx :=
  div_nonneg (jacobiCrossTerm_nonneg ctx) (jacobiDiagBackground_pos ctx).le

noncomputable def jacobiOneStepGain (ctx : LocalContext ι) : ℝ :=
  max (jacobiForegroundCoeff ctx) (jacobiBackgroundCoeff ctx)

theorem jacobiOneStepGain_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ jacobiOneStepGain ctx :=
  le_trans (jacobiForegroundCoeff_nonneg ctx) (le_max_left _ _)

theorem jacobiSpectralRadius_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ jacobiSpectralRadius ctx :=
  div_nonneg (jacobiCrossTerm_nonneg ctx) (Real.sqrt_nonneg _)

theorem jacobiDifferenceMap_infty_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (g : LocalUnknown) :
    localInfinityNorm (jacobiDifferenceMap ctx g) ≤
      jacobiOneStepGain ctx * localInfinityNorm g := by
  refine max_le ?_ ?_
  · calc |foreground (jacobiDifferenceMap ctx g)|
        = jacobiForegroundCoeff ctx * |background g| := by
          rw [jacobiDifferenceMap_foreground]
          simp [abs_mul, abs_of_nonneg (jacobiForegroundCoeff_nonneg ctx)]
      _ ≤ jacobiOneStepGain ctx * localInfinityNorm g :=
          mul_le_mul (le_max_left _ _) (background_abs_le_localInfinityNorm g)
            (abs_nonneg _) (jacobiOneStepGain_nonneg ctx)
  · calc |background (jacobiDifferenceMap ctx g)|
        = jacobiBackgroundCoeff ctx * |foreground g| := by
          rw [jacobiDifferenceMap_background]
          simp [abs_mul, abs_of_nonneg (jacobiBackgroundCoeff_nonneg ctx)]
      _ ≤ jacobiOneStepGain ctx * localInfinityNorm g :=
          mul_le_mul (le_max_right _ _) (foreground_abs_le_localInfinityNorm g)
            (abs_nonneg _) (jacobiOneStepGain_nonneg ctx)

theorem jacobiOneStep_infty_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (x y : LocalUnknown) :
    localInfinityNorm (jacobiStep ctx x - jacobiStep ctx y) ≤
      jacobiOneStepGain ctx * localInfinityNorm (x - y) := by
  rw [jacobiStep_sub_eq]; exact jacobiDifferenceMap_infty_bound ctx (x - y)

@[simp] theorem jacobiIterate_zero (ctx : LocalContext ι) (x : LocalUnknown) :
    jacobiIterate ctx 0 x = x := rfl

@[simp] theorem jacobiIterate_succ (ctx : LocalContext ι) (k : Nat) (x : LocalUnknown) :
    jacobiIterate ctx (k + 1) x = jacobiIterate ctx k (jacobiStep ctx x) := by
  simp [jacobiIterate, Function.iterate_succ_apply]

theorem jacobiIterate_closedFormSolution
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (k : Nat) :
    jacobiIterate ctx k (closedFormSolution ctx) = closedFormSolution ctx := by
  induction k with
  | zero => rfl
  | succ k ih => simp [jacobiStep_closedFormSolution, ih]

theorem jacobiIterate_two_mul_infty_contraction
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (m : Nat) (x y : LocalUnknown) :
    localInfinityNorm (jacobiIterate ctx (2 * m) x - jacobiIterate ctx (2 * m) y) =
      jacobiSpectralRadiusSq ctx ^ m * localInfinityNorm (x - y) := by
  induction m with
  | zero => simp [jacobiIterate]
  | succ m ih =>
      have hx : jacobiIterate ctx (2 * (m + 1)) x =
          jacobiStep ctx (jacobiStep ctx (jacobiIterate ctx (2 * m) x)) := by
        rw [show 2 * (m + 1) = 2 + 2 * m by omega, jacobiIterate, Function.iterate_add_apply]; rfl
      have hy : jacobiIterate ctx (2 * (m + 1)) y =
          jacobiStep ctx (jacobiStep ctx (jacobiIterate ctx (2 * m) y)) := by
        rw [show 2 * (m + 1) = 2 + 2 * m by omega, jacobiIterate, Function.iterate_add_apply]; rfl
      rw [hx, hy, jacobiTwoStep_infty_contraction, ih, pow_succ]; ring

theorem jacobiIterate_two_mul_error_eq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (m : Nat) (x : LocalUnknown) :
    localInfinityNorm (jacobiIterate ctx (2 * m) x - closedFormSolution ctx) =
      jacobiSpectralRadiusSq ctx ^ m * localInfinityNorm (x - closedFormSolution ctx) := by
  simpa [jacobiIterate_closedFormSolution] using
    jacobiIterate_two_mul_infty_contraction ctx m x (closedFormSolution ctx)

theorem jacobiIterate_two_mul_add_one_error_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (m : Nat) (x : LocalUnknown) :
    localInfinityNorm (jacobiIterate ctx (2 * m + 1) x - closedFormSolution ctx) ≤
      jacobiOneStepGain ctx * jacobiSpectralRadiusSq ctx ^ m *
        localInfinityNorm (x - closedFormSolution ctx) := by
  have hx : jacobiIterate ctx (2 * m + 1) x =
      jacobiStep ctx (jacobiIterate ctx (2 * m) x) := by
    rw [show 2 * m + 1 = 1 + 2 * m by omega, jacobiIterate, Function.iterate_add_apply]; rfl
  calc localInfinityNorm (jacobiIterate ctx (2 * m + 1) x - closedFormSolution ctx)
      = localInfinityNorm (jacobiStep ctx (jacobiIterate ctx (2 * m) x) -
          jacobiStep ctx (closedFormSolution ctx)) := by rw [hx, jacobiStep_closedFormSolution]
    _ ≤ jacobiOneStepGain ctx * localInfinityNorm _ := jacobiOneStep_infty_bound ctx _ _
    _ = _ := by rw [jacobiIterate_two_mul_error_eq]; ring

theorem jacobiSpectralRadius_le_jacobiOneStepGain
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    jacobiSpectralRadius ctx ≤ jacobiOneStepGain ctx := by
  nlinarith [jacobiSpectralRadius_nonneg ctx, jacobiOneStepGain_nonneg ctx,
    show jacobiSpectralRadius ctx ^ 2 ≤ jacobiOneStepGain ctx ^ 2 from by
      rw [jacobiSpectralRadius_sq, jacobiOneStepGain, pow_two]
      exact mul_le_mul (le_max_left _ _) (le_max_right _ _)
        (jacobiBackgroundCoeff_nonneg ctx)
        (le_trans (jacobiForegroundCoeff_nonneg ctx) (le_max_left _ _))]

private theorem jacobiSpectralRadiusSq_pow
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (m : Nat) :
    jacobiSpectralRadiusSq ctx ^ m = jacobiSpectralRadius ctx ^ (2 * m) := by
  rw [← jacobiSpectralRadius_sq, pow_mul]

theorem jacobiIterate_error_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown) :
    localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) ≤
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · simpa [jacobiSpectralRadiusSq_pow ctx m, pow_mul] using
      jacobiIterate_two_mul_add_one_error_le ctx m x
  · have hnorm := localInfinityNorm_nonneg (x - closedFormSolution ctx)
    have hpow := pow_nonneg (jacobiSpectralRadius_nonneg ctx) (2 * m + 1)
    calc
      localInfinityNorm (jacobiIterate ctx ((2 * m + 1) + 1) x - closedFormSolution ctx)
          = jacobiSpectralRadiusSq ctx ^ (m + 1) *
              localInfinityNorm (x - closedFormSolution ctx) := by
                rw [show (2 * m + 1) + 1 = 2 * (m + 1) by omega]
                simpa using jacobiIterate_two_mul_error_eq ctx (m + 1) x
      _ = jacobiSpectralRadius ctx ^ (2 * m + 2) *
            localInfinityNorm (x - closedFormSolution ctx) := by
              rw [jacobiSpectralRadiusSq_pow ctx (m + 1)]; congr 1
      _ = jacobiSpectralRadius ctx *
            (jacobiSpectralRadius ctx ^ (2 * m + 1) *
              localInfinityNorm (x - closedFormSolution ctx)) := by
                rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]; ring
      _ ≤ jacobiOneStepGain ctx *
            (jacobiSpectralRadius ctx ^ (2 * m + 1) *
              localInfinityNorm (x - closedFormSolution ctx)) :=
                mul_le_mul_of_nonneg_right
                  (jacobiSpectralRadius_le_jacobiOneStepGain ctx) (mul_nonneg hpow hnorm)
      _ = jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ (2 * m + 1) *
            localInfinityNorm (x - closedFormSolution ctx) := by ring

example (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 0) :
    jacobiSpectralRadius ctx = 0 :=
  jacobiSpectralRadius_eq_zero_of_alpha_zero ctx hα

example (ctx : LocalContext ι) [CoreMathAssumptions ctx] (hα : ctx.alphaCenter = 1) :
    jacobiSpectralRadius ctx = 0 :=
  jacobiSpectralRadius_eq_zero_of_alpha_one ctx hα

end LocalContext

end FastMLFE2.Theorems
