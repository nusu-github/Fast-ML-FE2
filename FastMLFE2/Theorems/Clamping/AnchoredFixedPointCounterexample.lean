import FastMLFE2.Theorems.Solvability.AnchoredClosedForm
import FastMLFE2.Theorems.Clamping.ClampLocal

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace AnchoredLocalContext

def binaryZeroRepairCtx (f b prior lam : ℝ) : AnchoredLocalContext Unit where
  alphaCenter := 0
  imageValue := 0
  alphaNeighbor := fun _ => 0
  fgNeighbor := fun _ => f
  bgNeighbor := fun _ => b
  epsilonR := 1
  omega := 0
  fgPrior := prior
  bgPrior := 0
  fgAnchorWeight := lam
  bgAnchorWeight := 0

instance binaryZeroRepairAssumptions (f b prior lam : ℝ) :
    CoreMathAssumptions (binaryZeroRepairCtx f b prior lam).toLocalContext where
  epsilonPos := by norm_num [binaryZeroRepairCtx]
  omegaNonneg := by norm_num [binaryZeroRepairCtx]
  alphaCenterBounded := by
    constructor <;> norm_num [binaryZeroRepairCtx]
  neighborNonempty := ⟨()⟩

noncomputable def binaryZeroRepairStep (prior lam : ℝ) (g : LocalUnknown) : LocalUnknown :=
  let ctx := binaryZeroRepairCtx (foreground g) (background g) prior lam
  clamp01 (ctx.closedFormSolution)

theorem binaryZeroRepair_closedForm (f b prior lam : ℝ) (hlam : 0 ≤ lam) :
    (binaryZeroRepairCtx f b prior lam).closedFormSolution =
      mkLocalUnknown ((f + lam * prior) / (1 + lam)) (b / (1 + 1)) := by
  have := AnchoredLocalContext.closedFormSolution_eq_of_alpha_zero
      (ctx := binaryZeroRepairCtx f b prior lam) hlam (by norm_num [binaryZeroRepairCtx]) rfl
  simp [binaryZeroRepairCtx, mkLocalUnknown] at this ⊢
  exact this

theorem binaryZeroRepair_step_const (f b prior lam : ℝ) (hlam : 0 ≤ lam) :
    binaryZeroRepairStep prior lam (mkLocalUnknown f b) =
      mkLocalUnknown (clamp01Scalar ((f + lam * prior) / (1 + lam))) (clamp01Scalar (b / 2)) := by
  rw [binaryZeroRepairStep, binaryZeroRepair_closedForm _ _ _ _ hlam]
  simp only [one_add_one_eq_two]
  ext i <;> fin_cases i <;>
    simp [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]

theorem binaryZeroRepair_fixedPoint_prior
    {prior lam : ℝ} (hprior0 : 0 ≤ prior) (hprior1 : prior ≤ 1) (hlam : 0 < lam) :
    binaryZeroRepairStep prior lam (mkLocalUnknown prior 0) = mkLocalUnknown prior 0 := by
  rw [binaryZeroRepair_step_const _ _ _ _ hlam.le]
  ext i
  fin_cases i
  · have hfrac : (prior + lam * prior) / (1 + lam) = prior := by
      have hden : 1 + lam ≠ 0 := by linarith
      field_simp [hden]
    rw [hfrac]
    simpa using
      FastMLFE2.Theorems.LocalContext.clamp01Scalar_eq_self_of_mem_Icc hprior0 hprior1
  · simp [mkLocalUnknown, clamp01Scalar]

theorem binaryZeroRepair_fixedPoint_iff
    {f prior lam : ℝ}
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hprior0 : 0 ≤ prior) (hprior1 : prior ≤ 1)
    (hlam : 0 < lam) :
    binaryZeroRepairStep prior lam (mkLocalUnknown f 0) = mkLocalUnknown f 0 ↔ f = prior := by
  rw [binaryZeroRepair_step_const _ _ _ _ hlam.le]
  constructor
  · intro h
    have hfg := congrArg foreground h
    simp [foreground, mkLocalUnknown] at hfg
    have hclamp :
        clamp01Scalar ((f + lam * prior) / (1 + lam)) = f := hfg
    have hmem :
        clamp01Scalar ((f + lam * prior) / (1 + lam)) = (f + lam * prior) / (1 + lam) := by
      apply FastMLFE2.Theorems.LocalContext.clamp01Scalar_eq_self_of_mem_Icc
      · have hnum : 0 ≤ f + lam * prior := by nlinarith
        have hden : 0 < 1 + lam := by linarith
        exact div_nonneg hnum hden.le
      · have hnum : f + lam * prior ≤ 1 + lam := by nlinarith
        have hden : 0 < 1 + lam := by linarith
        exact (div_le_one hden).2 hnum
    rw [hmem] at hclamp
    have hden : 1 + lam ≠ 0 := by linarith
    field_simp [hden] at hclamp
    nlinarith
  · intro hfp
    subst hfp
    ext i
    fin_cases i
    · have hfrac : (f + lam * f) / (1 + lam) = f := by
        have hden : 1 + lam ≠ 0 := by linarith
        field_simp [hden]
      rw [hfrac]
      simpa using
        FastMLFE2.Theorems.LocalContext.clamp01Scalar_eq_self_of_mem_Icc hf0 hf1
    · simp [mkLocalUnknown, clamp01Scalar]

end AnchoredLocalContext

end FastMLFE2.Theorems
