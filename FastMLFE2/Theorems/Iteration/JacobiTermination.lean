import FastMLFE2.Theorems.Iteration.JacobiContraction
import FastMLFE2.Theorems.Iteration.ContractionBounds

namespace FastMLFE2.Theorems

/-!
Early-termination iteration budget for per-pixel Jacobi.

Bridges the abstract `scale_mul_pow_le_of_log_threshold` theorem in `ContractionBounds`
to the concrete `jacobiIterate` error bound in `JacobiContraction`.
-/

open FastMLFE2.Core
open FastMLFE2.Core.LocalContext
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- Given an initial error bound `scale` and target tolerance `eta`, the Jacobi
iterate reaches `‖x_k − x*‖∞ ≤ eta` after
  `k ≥ 1 + log(scale / eta) / log(1 / ρ)` steps,
where `ρ = jacobiOneStepGain`. -/
theorem jacobiIterate_terminationBound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    {scale eta : ℝ} (hscale : 0 < scale) (heta : 0 < eta)
    {k : ℕ}
    (hk : 1 + Real.log (scale / eta) / Real.log (1 / jacobiOneStepGain ctx) ≤ (k + 1 : ℝ))
    (hgain_lt : jacobiOneStepGain ctx < 1)
    (x : LocalUnknown)
    (hx : localInfinityNorm (x - closedFormSolution ctx) ≤ scale) :
    localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) ≤ eta := by
  have hgain_nonneg := jacobiOneStepGain_nonneg ctx
  have hspectral_nonneg := jacobiSpectralRadius_nonneg ctx
  have hspectral_le := jacobiSpectralRadius_le_jacobiOneStepGain ctx
  have herr := jacobiIterate_error_le ctx k x
  have hnorm_nonneg : 0 ≤ localInfinityNorm (x - closedFormSolution ctx) :=
    localInfinityNorm_nonneg (x - closedFormSolution ctx)
  have hpow_le :
      jacobiSpectralRadius ctx ^ k ≤ jacobiOneStepGain ctx ^ k :=
    pow_le_pow_left₀ hspectral_nonneg hspectral_le k
  have hscale_bound :
      localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) ≤
        jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k * scale := by
    have hmul :
        jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
            localInfinityNorm (x - closedFormSolution ctx) ≤
          jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k *
            localInfinityNorm (x - closedFormSolution ctx) := by
      have hinner :
          jacobiSpectralRadius ctx ^ k * localInfinityNorm (x - closedFormSolution ctx) ≤
            jacobiOneStepGain ctx ^ k * localInfinityNorm (x - closedFormSolution ctx) :=
        mul_le_mul_of_nonneg_right hpow_le hnorm_nonneg
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinner hgain_nonneg
    calc
      localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx)
          ≤ jacobiOneStepGain ctx * jacobiSpectralRadius ctx ^ k *
              localInfinityNorm (x - closedFormSolution ctx) := herr
      _ ≤ jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k *
            localInfinityNorm (x - closedFormSolution ctx) := hmul
      _ ≤ jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k * scale :=
        mul_le_mul_of_nonneg_left hx (mul_nonneg hgain_nonneg (pow_nonneg hgain_nonneg _))
  by_cases hgain0 : jacobiOneStepGain ctx = 0
  · have hzero :
        localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) ≤ 0 := by
      simpa [hgain0] using hscale_bound
    exact hzero.trans heta.le
  · have hgain_pos : 0 < jacobiOneStepGain ctx :=
      lt_of_le_of_ne hgain_nonneg (Ne.symm hgain0)
    have hgain_drop :
        jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k * scale ≤
          scale * jacobiOneStepGain ctx ^ k := by
      have hpow_scale_nonneg : 0 ≤ jacobiOneStepGain ctx ^ k * scale :=
        mul_nonneg (pow_nonneg hgain_nonneg _) hscale.le
      nlinarith
    have hthreshold :
        scale * jacobiOneStepGain ctx ^ k ≤ eta :=
      scale_mul_pow_le_of_log_threshold hscale heta hgain_pos hgain_lt hk
    exact hscale_bound.trans (hgain_drop.trans hthreshold)

end LocalContext

end FastMLFE2.Theorems
