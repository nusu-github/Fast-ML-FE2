import FastMLFE2.Theorems.CompositingError
import FastMLFE2.Theorems.ContractionBounds
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
  have : |foreground (jacobiIterate ctx (k + 1) x) - foreground (closedFormSolution ctx)| =
      |foreground (jacobiIterate ctx (k + 1) x - closedFormSolution ctx)| := by simp [foreground]
  rw [this]
  exact (foreground_abs_le_localInfinityNorm _).trans (jacobiIterate_error_le ctx k x)

theorem abs_background_sub_closedForm_le_iterateError
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (k : Nat) (x : LocalUnknown) :
    |background (jacobiIterate ctx (k + 1) x) - background (closedFormSolution ctx)| ≤
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  have : |background (jacobiIterate ctx (k + 1) x) - background (closedFormSolution ctx)| =
      |background (jacobiIterate ctx (k + 1) x - closedFormSolution ctx)| := by simp [background]
  rw [this]
  exact (background_abs_le_localInfinityNorm _).trans (jacobiIterate_error_le ctx k x)

theorem localInfinityNorm_sub_le_one_of_boxed
    (g h : LocalUnknown)
    (hg : clamp01 g = g)
    (hh : clamp01 h = h) :
    localInfinityNorm (g - h) ≤ 1 := by
  rcases (clamp01_eq_self_iff (g := g)).1 hg with ⟨⟨hfg0, hfg1⟩, ⟨hbg0, hbg1⟩⟩
  rcases (clamp01_eq_self_iff (g := h)).1 hh with ⟨⟨hfg0', hfg1'⟩, ⟨hbg0', hbg1'⟩⟩
  refine max_le ?_ ?_
  · have : foreground (g - h) = foreground g - foreground h := by simp [foreground]
    rw [this]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · have : background (g - h) = background g - background h := by simp [background]
    rw [this]; exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

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
  set err := jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
    localInfinityNorm (x - closedFormSolution ctx)
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  calc _ ≤ ctx.alphaCenter * |foreground (jacobiIterate ctx (k + 1) x) -
            foreground (closedFormSolution ctx)| +
          (1 - ctx.alphaCenter) * |background (jacobiIterate ctx (k + 1) x) -
            background (closedFormSolution ctx)| :=
        abs_compose_sub_compose_le_authored hα.1 hα.2
    _ ≤ ctx.alphaCenter * err + (1 - ctx.alphaCenter) * err :=
        add_le_add
          (mul_le_mul_of_nonneg_left (abs_foreground_sub_closedForm_le_iterateError ctx k x) hα.1)
          (mul_le_mul_of_nonneg_left (abs_background_sub_closedForm_le_iterateError ctx k x)
            (sub_nonneg.mpr hα.2))
    _ = err := by ring

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
        (background (closedFormSolution ctx))| ≤ eta :=
  (jacobiIterate_compose_error_le ctx k x).trans hbound

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
      jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k :=
  jacobiIterate_compose_error_le_of_bound ctx k x
    ((mul_le_mul_of_nonneg_left
      (localInfinityNorm_sub_le_one_of_boxed x (closedFormSolution ctx) hx hfixed)
      (mul_nonneg (jacobiOneStepGain_nonneg ctx)
        (pow_nonneg (jacobiSpectralRadius_nonneg ctx) _))).trans (mul_one _).le)

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
        (background (closedFormSolution ctx))| ≤ eta :=
  jacobiIterate_compose_error_le_of_bound ctx k x (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      scale_mul_pow_le_of_log_threshold hscale heta hrho0 hrho1 hk)

end LocalContext

end FastMLFE2.Theorems
