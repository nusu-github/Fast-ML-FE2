import FastMLFE2.Theorems.CompositingError
import FastMLFE2.Theorems.JacobiContraction
import FastMLFE2.Theorems.ClosedFormBox

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Compositing

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem abs_foreground_sub_closedForm_le_iterateError
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown) :
    |foreground (jacobiIterate ctx (k + 1) x) - foreground (closedFormSolution ctx)| ≤
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  calc
    |foreground (jacobiIterate ctx (k + 1) x) - foreground (closedFormSolution ctx)|
        = |foreground (jacobiIterate ctx (k + 1) x - closedFormSolution ctx)| := by
            simp [foreground]
    _ ≤ localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) := by
      exact foreground_abs_le_localInfinityNorm _
    _ ≤ jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
          localInfinityNorm (x - closedFormSolution ctx) := by
      exact jacobiIterate_error_le ctx k x

theorem abs_background_sub_closedForm_le_iterateError
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown) :
    |background (jacobiIterate ctx (k + 1) x) - background (closedFormSolution ctx)| ≤
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  calc
    |background (jacobiIterate ctx (k + 1) x) - background (closedFormSolution ctx)|
        = |background (jacobiIterate ctx (k + 1) x - closedFormSolution ctx)| := by
            simp [background]
    _ ≤ localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) := by
      exact background_abs_le_localInfinityNorm _
    _ ≤ jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
          localInfinityNorm (x - closedFormSolution ctx) := by
      exact jacobiIterate_error_le ctx k x

theorem localInfinityNorm_sub_le_one_of_boxed
    (g h : LocalUnknown)
    (hg : clamp01 g = g)
    (hh : clamp01 h = h) :
    localInfinityNorm (g - h) ≤ 1 := by
  rcases (clamp01_eq_self_iff (g := g)).1 hg with ⟨⟨hfg0, hfg1⟩, ⟨hbg0, hbg1⟩⟩
  rcases (clamp01_eq_self_iff (g := h)).1 hh with ⟨⟨hfg0', hfg1'⟩, ⟨hbg0', hbg1'⟩⟩
  refine max_le ?_ ?_
  · have hlow : -1 ≤ foreground (g - h) := by
      have : -1 ≤ foreground g - foreground h := by
        nlinarith
      simpa [foreground]
    have hupp : foreground (g - h) ≤ 1 := by
      have : foreground g - foreground h ≤ 1 := by
        nlinarith
      simpa [foreground]
    simpa [foreground] using (abs_le.2 ⟨hlow, hupp⟩)
  · have hlow : -1 ≤ background (g - h) := by
      have : -1 ≤ background g - background h := by
        nlinarith
      simpa [background]
    have hupp : background (g - h) ≤ 1 := by
      have : background g - background h ≤ 1 := by
        nlinarith
      simpa [background]
    simpa [background] using (abs_le.2 ⟨hlow, hupp⟩)

private theorem scale_mul_pow_le_of_log_threshold
    {scale eta rho : ℝ}
    {k : Nat}
    (hscale : 0 < scale)
    (heta : 0 < eta)
    (hrho0 : 0 < rho)
    (hrho1 : rho < 1)
    (hk :
      1 + Real.log (scale / eta) / Real.log (1 / rho) ≤ (k + 1 : ℝ)) :
    scale * rho ^ k ≤ eta := by
  have hlogDenPos : 0 < Real.log (1 / rho) := by
    have hInv : 1 < 1 / rho := by
      exact one_lt_one_div hrho0 hrho1
    exact Real.log_pos hInv
  have hk' : Real.log (scale / eta) / Real.log (1 / rho) ≤ (k : ℝ) := by
    nlinarith
  have hlog :
      Real.log (scale / eta) ≤ (k : ℝ) * Real.log (1 / rho) := by
    exact (div_le_iff₀ hlogDenPos).1 hk'
  have hdivle :
      scale / eta ≤ ((1 / rho : ℝ) ^ (k : ℝ)) := by
    have hposL : 0 < scale / eta := div_pos hscale heta
    have hposR : 0 < ((1 / rho : ℝ) ^ (k : ℝ)) := by
      exact Real.rpow_pos_of_pos (one_div_pos.mpr hrho0) _
    have hlogle :
        Real.log (scale / eta) ≤ Real.log (((1 / rho : ℝ) ^ (k : ℝ))) := by
      rw [Real.log_rpow (one_div_pos.mpr hrho0) (k : ℝ)]
      exact hlog
    exact (Real.strictMonoOn_log.le_iff_le hposL hposR).1 hlogle
  have hdivle' : scale / eta ≤ (1 / rho : ℝ) ^ k := by
    simpa [Real.rpow_natCast] using hdivle
  have hscalele : scale ≤ eta * ((1 / rho : ℝ) ^ k) := by
    have hscalele' : scale ≤ ((1 / rho : ℝ) ^ k) * eta := by
      exact (div_le_iff₀ heta).1 hdivle'
    simpa [mul_comm] using hscalele'
  have hrhoPowPos : 0 < rho ^ k := pow_pos hrho0 _
  have hunit : ((1 / rho : ℝ) ^ k) * rho ^ k = 1 := by
    rw [one_div_pow]
    field_simp [pow_ne_zero k hrho0.ne']
  calc
    scale * rho ^ k ≤ (eta * ((1 / rho : ℝ) ^ k)) * rho ^ k := by
      exact mul_le_mul_of_nonneg_right hscalele (le_of_lt hrhoPowPos)
    _ = eta * (((1 / rho : ℝ) ^ k) * rho ^ k) := by ring
    _ = eta := by rw [hunit, mul_one]

theorem jacobiIterate_compose_error_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown) :
    |compose ctx.alphaCenter
        (foreground (jacobiIterate ctx (k + 1) x))
        (background (jacobiIterate ctx (k + 1) x)) -
      compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx))| ≤
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  let err :=
    jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
      localInfinityNorm (x - closedFormSolution ctx)
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  have hfg :
      |foreground (jacobiIterate ctx (k + 1) x) - foreground (closedFormSolution ctx)| ≤ err := by
    simpa [err] using abs_foreground_sub_closedForm_le_iterateError (ctx := ctx) k x
  have hbg :
      |background (jacobiIterate ctx (k + 1) x) - background (closedFormSolution ctx)| ≤ err := by
    simpa [err] using abs_background_sub_closedForm_le_iterateError (ctx := ctx) k x
  calc
    |compose ctx.alphaCenter
        (foreground (jacobiIterate ctx (k + 1) x))
        (background (jacobiIterate ctx (k + 1) x)) -
      compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx))|
        ≤ ctx.alphaCenter *
            |foreground (jacobiIterate ctx (k + 1) x) - foreground (closedFormSolution ctx)| +
          (1 - ctx.alphaCenter) *
            |background (jacobiIterate ctx (k + 1) x) - background (closedFormSolution ctx)| := by
              exact abs_compose_sub_compose_le_authored hα.1 hα.2
    _ ≤ ctx.alphaCenter * err + (1 - ctx.alphaCenter) * err := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfg hα.1)
        (mul_le_mul_of_nonneg_left hbg (sub_nonneg.mpr hα.2))
    _ = err := by
      unfold err
      ring

theorem jacobiIterate_compose_error_le_of_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown)
    {eta : ℝ}
    (hbound :
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) ≤ eta) :
    |compose ctx.alphaCenter
        (foreground (jacobiIterate ctx (k + 1) x))
        (background (jacobiIterate ctx (k + 1) x)) -
      compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx))| ≤ eta := by
  exact le_trans (jacobiIterate_compose_error_le (ctx := ctx) k x) hbound

theorem jacobiIterate_compose_error_le_of_boxed
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown)
    (hx : clamp01 x = x)
    (hfixed : clamp01 (closedFormSolution ctx) = closedFormSolution ctx) :
    |compose ctx.alphaCenter
        (foreground (jacobiIterate ctx (k + 1) x))
        (background (jacobiIterate ctx (k + 1) x)) -
      compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx))| ≤
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k := by
  have hnorm :
      localInfinityNorm (x - closedFormSolution ctx) ≤ 1 := by
    exact localInfinityNorm_sub_le_one_of_boxed x (closedFormSolution ctx) hx hfixed
  have hscale_nonneg :
      0 ≤ jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k := by
    exact mul_nonneg (jacobiOneStepGain_nonneg ctx)
      (pow_nonneg (jacobiSpectralRadius_nonneg ctx) _)
  calc
    |compose ctx.alphaCenter
        (foreground (jacobiIterate ctx (k + 1) x))
        (background (jacobiIterate ctx (k + 1) x)) -
      compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx))|
        ≤ jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
            localInfinityNorm (x - closedFormSolution ctx) := by
              exact jacobiIterate_compose_error_le (ctx := ctx) k x
    _ ≤ jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k * 1 := by
      exact mul_le_mul_of_nonneg_left hnorm hscale_nonneg
    _ = jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k := by ring

theorem jacobiIterate_compose_error_le_of_log_threshold
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown)
    {eta : ℝ}
    (hscale :
      0 < jacobiOneStepGain ctx * localInfinityNorm (x - closedFormSolution ctx))
    (heta : 0 < eta)
    (hrho0 : 0 < jacobiSpectralRadius ctx)
    (hrho1 : jacobiSpectralRadius ctx < 1)
    (hk :
      1 + Real.log
            ((jacobiOneStepGain ctx * localInfinityNorm (x - closedFormSolution ctx)) / eta) /
            Real.log (1 / jacobiSpectralRadius ctx)
          ≤ (k + 1 : ℝ)) :
    |compose ctx.alphaCenter
        (foreground (jacobiIterate ctx (k + 1) x))
        (background (jacobiIterate ctx (k + 1) x)) -
      compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx))| ≤ eta := by
  have hbound :
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) ≤ eta := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      scale_mul_pow_le_of_log_threshold
        (scale := jacobiOneStepGain ctx * localInfinityNorm (x - closedFormSolution ctx))
        (eta := eta)
        (rho := jacobiSpectralRadius ctx)
        (k := k)
        hscale heta hrho0 hrho1 hk
  exact jacobiIterate_compose_error_le_of_bound (ctx := ctx) k x hbound

end LocalContext

end FastMLFE2.Theorems
