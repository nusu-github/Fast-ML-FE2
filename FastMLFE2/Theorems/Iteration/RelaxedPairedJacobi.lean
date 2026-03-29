import FastMLFE2.Theorems.Iteration.JacobiContraction
import FastMLFE2.Theorems.Iteration.ContractionBounds
import FastMLFE2.Theorems.Clamping.ClampPlacement
import FastMLFE2.Theorems.Clamping.ClosedFormBox
import FastMLFE2.Theorems.Approximation.BleedThrough

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- The two-step local Jacobi map. -/
noncomputable def pairedJacobiStep (ctx : LocalContext ι) : LocalUnknown → LocalUnknown :=
  fun x => jacobiStep ctx (jacobiStep ctx x)

/-- Relaxed two-step Jacobi update `x ↦ x + r (J₂(x) - x)`. -/
noncomputable def relaxedPairedJacobiStep
    (ctx : LocalContext ι) (r : ℝ) : LocalUnknown → LocalUnknown :=
  relaxedUpdate r (pairedJacobiStep ctx)

/-- `k` relaxed two-step Jacobi updates. -/
noncomputable def relaxedPairedJacobiIterate
    (ctx : LocalContext ι) (r : ℝ) (k : Nat) : LocalUnknown → LocalUnknown :=
  Nat.iterate (relaxedPairedJacobiStep ctx r) k

/-- Clamp once after `k` relaxed two-step Jacobi updates. -/
noncomputable def endClampedRelaxedPairedJacobiIterate
    (ctx : LocalContext ι) (r : ℝ) (k : Nat) (x : LocalUnknown) : LocalUnknown :=
  clamp01 (relaxedPairedJacobiIterate ctx r k x)

theorem norm_eq_localInfinityNorm (g : LocalUnknown) :
    ‖g‖ = localInfinityNorm g := by
  rw [Pi.norm_def]
  rw [show (Finset.univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 2)) by decide]
  simp [localInfinityNorm, foreground, background]

theorem pairedJacobiStep_eq_iterate_two
    (ctx : LocalContext ι) (x : LocalUnknown) :
    pairedJacobiStep ctx x = jacobiIterate ctx 2 x := by
  simp [pairedJacobiStep, jacobiIterate, Function.comp]

theorem pairedJacobiStep_closedFormSolution
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    pairedJacobiStep ctx (closedFormSolution ctx) = closedFormSolution ctx := by
  simp [pairedJacobiStep, jacobiStep_closedFormSolution]

theorem pairedJacobiStep_infty_contraction
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (x y : LocalUnknown) :
    localInfinityNorm (pairedJacobiStep ctx x - pairedJacobiStep ctx y) ≤
      jacobiSpectralRadiusSq ctx * localInfinityNorm (x - y) := by
  rw [pairedJacobiStep]
  simpa using le_of_eq (jacobiTwoStep_infty_contraction ctx x y)

theorem pairedJacobiStep_norm_contraction
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (x y : LocalUnknown) :
    ‖pairedJacobiStep ctx x - pairedJacobiStep ctx y‖ ≤
      jacobiSpectralRadiusSq ctx * ‖x - y‖ := by
  rw [norm_eq_localInfinityNorm, norm_eq_localInfinityNorm]
  exact pairedJacobiStep_infty_contraction ctx x y

theorem relaxedPairedJacobiStep_contractive_of_lt_lambdaMax
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] {r : ℝ}
    (hr0 : 0 < r)
    (hrmax : r < relaxationLambdaMax (jacobiSpectralRadiusSq ctx)) :
    relaxationContractionRate r (jacobiSpectralRadiusSq ctx) < 1 ∧
      ∀ x y,
        localInfinityNorm (relaxedPairedJacobiStep ctx r x - relaxedPairedJacobiStep ctx r y) ≤
          relaxationContractionRate r (jacobiSpectralRadiusSq ctx) *
            localInfinityNorm (x - y) := by
  have hq0 : 0 ≤ jacobiSpectralRadiusSq ctx := by
    rw [jacobiSpectralRadiusSq_eq]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)))
  have hq1 : jacobiSpectralRadiusSq ctx < 1 := by
    have hρ := jacobiSpectralRadius_lt_one ctx
    nlinarith [jacobiSpectralRadius_nonneg ctx, jacobiSpectralRadius_sq (ctx := ctx)]
  rcases relaxedUpdate_contractive_of_lt_lambdaMax
      (J := pairedJacobiStep ctx)
      (q := jacobiSpectralRadiusSq ctx)
      (r := r)
      (pairedJacobiStep_norm_contraction ctx)
      hq0 hq1 hr0 hrmax with ⟨hρ, hLip⟩
  refine ⟨hρ, ?_⟩
  intro x y
  specialize hLip x y
  simpa [relaxedPairedJacobiStep, norm_eq_localInfinityNorm] using hLip

theorem closedFormSolution_fixed_of_relaxedPairedJacobiStep
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (r : ℝ) :
    relaxedPairedJacobiStep ctx r (closedFormSolution ctx) = closedFormSolution ctx := by
  simp [relaxedPairedJacobiStep, relaxedUpdate, pairedJacobiStep_closedFormSolution]

@[simp] theorem relaxedPairedJacobiIterate_zero
    (ctx : LocalContext ι) (r : ℝ) (x : LocalUnknown) :
    relaxedPairedJacobiIterate ctx r 0 x = x := rfl

@[simp] theorem relaxedPairedJacobiIterate_succ
    (ctx : LocalContext ι) (r : ℝ) (k : Nat) (x : LocalUnknown) :
    relaxedPairedJacobiIterate ctx r (k + 1) x =
      relaxedPairedJacobiIterate ctx r k (relaxedPairedJacobiStep ctx r x) := by
  simp [relaxedPairedJacobiIterate, Function.iterate_succ_apply]

theorem relaxedPairedJacobiIterate_closedFormSolution
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (r : ℝ) (k : Nat) :
    relaxedPairedJacobiIterate ctx r k (closedFormSolution ctx) = closedFormSolution ctx := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      simp [relaxedPairedJacobiIterate_succ, closedFormSolution_fixed_of_relaxedPairedJacobiStep,
        ih]

theorem relaxedPairedJacobiIterate_error_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] {r : ℝ}
    (hr0 : 0 < r)
    (hrmax : r < relaxationLambdaMax (jacobiSpectralRadiusSq ctx))
    (k : Nat) (x : LocalUnknown) :
    localInfinityNorm (relaxedPairedJacobiIterate ctx r k x - closedFormSolution ctx) ≤
      relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  rcases relaxedPairedJacobiStep_contractive_of_lt_lambdaMax (ctx := ctx) hr0 hrmax with
    ⟨_, hLip⟩
  revert x
  induction k with
  | zero =>
      intro x
      simp
  | succ k ih =>
      intro x
      have hLip' :
          localInfinityNorm (relaxedPairedJacobiStep ctx r x - closedFormSolution ctx) ≤
            relaxationContractionRate r (jacobiSpectralRadiusSq ctx) *
              localInfinityNorm (x - closedFormSolution ctx) := by
        simpa [closedFormSolution_fixed_of_relaxedPairedJacobiStep (ctx := ctx) (r := r)] using
          hLip x (closedFormSolution ctx)
      have hrate_nonneg : 0 ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k := by
        have hq0 : 0 ≤ jacobiSpectralRadiusSq ctx := by
          rw [jacobiSpectralRadiusSq_eq]
          exact div_nonneg (sq_nonneg _)
            (le_of_lt (mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)))
        have hrate0 : 0 ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) :=
          add_nonneg (abs_nonneg _) (mul_nonneg hr0.le hq0)
        exact pow_nonneg hrate0 _
      calc
        localInfinityNorm
            (relaxedPairedJacobiIterate ctx r k
                (relaxedPairedJacobiStep ctx r x) - closedFormSolution ctx)
          = localInfinityNorm
              (relaxedPairedJacobiIterate ctx r k
                  (relaxedPairedJacobiStep ctx r x) -
                relaxedPairedJacobiIterate ctx r k (closedFormSolution ctx)) := by
              rw [relaxedPairedJacobiIterate_closedFormSolution (ctx := ctx) (r := r) k]
        _ ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k *
              localInfinityNorm
                (relaxedPairedJacobiStep ctx r x -
                  closedFormSolution ctx) := by
              simpa [relaxedPairedJacobiIterate_closedFormSolution (ctx := ctx) (r := r) k]
                using ih (relaxedPairedJacobiStep ctx r x)
        _ ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k *
              (relaxationContractionRate r (jacobiSpectralRadiusSq ctx) *
                localInfinityNorm (x - closedFormSolution ctx)) := by
              exact mul_le_mul_of_nonneg_left hLip' hrate_nonneg
        _ = relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ (k + 1) *
              localInfinityNorm (x - closedFormSolution ctx) := by
              ring

theorem endClampedRelaxedPairedJacobiIterate_error_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] {r : ℝ}
    (hr0 : 0 < r)
    (hrmax : r < relaxationLambdaMax (jacobiSpectralRadiusSq ctx))
    (k : Nat) (x : LocalUnknown)
    (hfixed : clamp01 (closedFormSolution ctx) = closedFormSolution ctx) :
    localInfinityNorm
        (endClampedRelaxedPairedJacobiIterate ctx r k x - closedFormSolution ctx) ≤
      relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := by
  calc
    localInfinityNorm
        (endClampedRelaxedPairedJacobiIterate ctx r k x - closedFormSolution ctx)
      = localInfinityNorm
          (clamp01 (relaxedPairedJacobiIterate ctx r k x) -
            clamp01 (closedFormSolution ctx)) := by
            simp [endClampedRelaxedPairedJacobiIterate, hfixed]
    _ ≤ localInfinityNorm
          (relaxedPairedJacobiIterate ctx r k x - closedFormSolution ctx) :=
        clamp01_nonexpansive _ _
    _ ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k *
          localInfinityNorm (x - closedFormSolution ctx) :=
        relaxedPairedJacobiIterate_error_le (ctx := ctx) hr0 hrmax k x

theorem endClampedRelaxedPairedJacobiIterate_error_le_of_boxed
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] {r : ℝ}
    (hr0 : 0 < r)
    (hrmax : r < relaxationLambdaMax (jacobiSpectralRadiusSq ctx))
    (k : Nat) (x : LocalUnknown)
    (hx : clamp01 x = x)
    (hfixed : clamp01 (closedFormSolution ctx) = closedFormSolution ctx) :
    localInfinityNorm
        (endClampedRelaxedPairedJacobiIterate ctx r k x - closedFormSolution ctx) ≤
      relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k := by
  refine (endClampedRelaxedPairedJacobiIterate_error_le
    (ctx := ctx) hr0 hrmax k x hfixed).trans ?_
  have hnorm :=
    localInfinityNorm_sub_le_one_of_boxed x (closedFormSolution ctx) hx hfixed
  have hq0 : 0 ≤ jacobiSpectralRadiusSq ctx := by
    rw [jacobiSpectralRadiusSq_eq]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (jacobiDiagForeground_pos ctx) (jacobiDiagBackground_pos ctx)))
  have hrate0 : 0 ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) :=
    add_nonneg (abs_nonneg _) (mul_nonneg hr0.le hq0)
  have hrate_nonneg : 0 ≤ relaxationContractionRate r (jacobiSpectralRadiusSq ctx) ^ k :=
    pow_nonneg hrate0 _
  exact (mul_le_mul_of_nonneg_left hnorm hrate_nonneg).trans (by simp)

end LocalContext

end FastMLFE2.Theorems
