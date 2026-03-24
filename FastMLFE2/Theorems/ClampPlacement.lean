import FastMLFE2.Canonical.ClampPlacement
import FastMLFE2.Theorems.ClosedForm
import FastMLFE2.Theorems.ClampLocal
import FastMLFE2.Theorems.JacobiContraction

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Canonical
open FastMLFE2.Assumptions
open FastMLFE2.Level

namespace LocalContext

noncomputable def rawStepGain {ι : Type*} [Fintype ι] (ctx : LocalContext ι) : ℝ :=
  (ctx.totalWeight * (ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter))) /
    closedFormDenom ctx

theorem clamp01Scalar_eq_projIcc (x : ℝ) :
    clamp01Scalar x = (Set.projIcc (0 : ℝ) 1 (by norm_num) x : ℝ) := by
  simp [clamp01Scalar, Set.coe_projIcc]

theorem clamp01Scalar_nonexpansive (x y : ℝ) :
    |clamp01Scalar x - clamp01Scalar y| ≤ |x - y| := by
  simpa [clamp01Scalar_eq_projIcc] using
    Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) (c := x) (d := y) (by norm_num)

theorem clamp01_nonexpansive (g h : LocalUnknown) :
    localInfinityNorm (clamp01 g - clamp01 h) ≤ localInfinityNorm (g - h) :=
  max_le
    ((clamp01Scalar_nonexpansive _ _).trans (le_max_left _ _))
    ((clamp01Scalar_nonexpansive _ _).trans (le_max_right _ _))

theorem rawStepGain_eq {ι : Type*} [Fintype ι] (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    rawStepGain ctx =
      (ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter)) /
        ctx.weightedMeanDenom := by
  rw [rawStepGain, closedFormDenom]
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  field_simp [htw0, LocalContext.weightedMeanDenom]

private theorem alphaQuadratic_le_max {ι : Type*} (ctx : LocalContext ι)
    (hα0 : 0 ≤ ctx.alphaCenter) (hα1 : ctx.alphaCenter ≤ 1) :
    ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 ≤
      max ctx.alphaCenter (1 - ctx.alphaCenter) := by
  by_cases hhalf : ctx.alphaCenter ≤ (1 : ℝ) / 2
  · rw [max_eq_right (by linarith)]; nlinarith
  · rw [max_eq_left (by linarith)]; nlinarith

theorem rawStepGain_ge_one {ι : Type*} [Fintype ι]
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    1 ≤ rawStepGain ctx := by
  rw [rawStepGain_eq]
  have hα := CoreMathAssumptions.alphaCenterBounded (ctx := ctx)
  have hden : 0 < ctx.weightedMeanDenom := LocalContext.weightedMeanDenom_pos ctx
  rw [le_div_iff₀ hden]
  simp [LocalContext.weightedMeanDenom]
  linarith [alphaQuadratic_le_max ctx hα.1 hα.2]

end LocalContext

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

def StateBound (δ : ℝ) (state : PixelState κ) : Prop :=
  ∀ p, LocalContext.localInfinityNorm (state p) ≤ δ

noncomputable def rawOvershoot (data : CanonicalPixelData κ η) (state : PixelState κ) (p : κ) : ℝ :=
  LocalContext.localInfinityNorm (data.rawStep state p - clamp01 (data.rawStep state p))

def RawOvershootBound (data : CanonicalPixelData κ η) (σ : ℝ) (state : PixelState κ) : Prop :=
  ∀ p, rawOvershoot data state p ≤ σ

theorem stateClamp01_nonexpansive
    (state₁ state₂ : PixelState κ) (δ : ℝ)
    (hδ : StateBound δ (fun p => state₁ p - state₂ p)) :
    StateBound δ
      (fun p => CanonicalPixelData.stateClamp01 state₁ p -
        CanonicalPixelData.stateClamp01 state₂ p) := fun p =>
  (LocalContext.clamp01_nonexpansive _ _).trans (hδ p)

end CanonicalPixelData

end FastMLFE2.Theorems
