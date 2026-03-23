import FastMLFE2.Theory.Canonical.ClampPlacement
import FastMLFE2.Theory.Theorems.ClosedForm
import FastMLFE2.Theory.Theorems.ClampLocal
import FastMLFE2.Theory.Theorems.JacobiContraction

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Canonical
open FastMLFE2.Theory.Assumptions
open FastMLFE2.Theory.Level

namespace LocalContext

noncomputable def rawStepGain {ι : Type*} [Fintype ι] (ctx : LocalContext ι) : ℝ :=
  (ctx.totalWeight * (ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter))) /
    closedFormDenom ctx

theorem clamp01Scalar_eq_projIcc
    (x : ℝ) :
    clamp01Scalar x = (Set.projIcc (0 : ℝ) 1 (by norm_num) x : ℝ) := by
  simp [clamp01Scalar, Set.coe_projIcc]

theorem clamp01Scalar_nonexpansive
    (x y : ℝ) :
    |clamp01Scalar x - clamp01Scalar y| ≤ |x - y| := by
  simpa [clamp01Scalar_eq_projIcc] using
    (Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) (c := x) (d := y) (by norm_num))

theorem clamp01_nonexpansive
    (g h : LocalUnknown) :
    localInfinityNorm (clamp01 g - clamp01 h) ≤
      localInfinityNorm (g - h) := by
  refine max_le ?_ ?_
  · calc
      |clamp01Scalar (foreground g) - clamp01Scalar (foreground h)| ≤
          |foreground g - foreground h| := clamp01Scalar_nonexpansive _ _
      _ ≤ max |foreground g - foreground h| |background g - background h| := le_max_left _ _
  · calc
      |clamp01Scalar (background g) - clamp01Scalar (background h)| ≤
          |background g - background h| := clamp01Scalar_nonexpansive _ _
      _ ≤ max |foreground g - foreground h| |background g - background h| := le_max_right _ _

theorem rawStepGain_eq
    {ι : Type*} [Fintype ι]
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    rawStepGain ctx =
      (ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter)) /
        (ctx.totalWeight + ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) := by
  rw [rawStepGain, closedFormDenom]
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  field_simp [htw0]

private theorem alphaQuadratic_le_max
    {ι : Type*}
    (ctx : LocalContext ι)
    (hα0 : 0 ≤ ctx.alphaCenter)
    (hα1 : ctx.alphaCenter ≤ 1) :
    ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 ≤
      max ctx.alphaCenter (1 - ctx.alphaCenter) := by
  by_cases hhalf : ctx.alphaCenter ≤ (1 : ℝ) / 2
  · rw [max_eq_right]
    · nlinarith
    · linarith
  · have hhalf' : (1 : ℝ) / 2 ≤ ctx.alphaCenter := le_of_not_ge hhalf
    rw [max_eq_left]
    · nlinarith
    · linarith

theorem rawStepGain_ge_one
    {ι : Type*} [Fintype ι]
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    1 ≤ rawStepGain ctx := by
  rw [rawStepGain_eq]
  have htw : 0 < ctx.totalWeight := totalWeight_pos ctx
  have hq :
      ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 ≤
        max ctx.alphaCenter (1 - ctx.alphaCenter) := by
    exact alphaQuadratic_le_max ctx
      (CoreMathAssumptions.alphaCenterBounded (ctx := ctx)).1
      (CoreMathAssumptions.alphaCenterBounded (ctx := ctx)).2
  have hden : 0 < ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) := by
    nlinarith [htw, sq_nonneg ctx.alphaCenter, sq_nonneg (1 - ctx.alphaCenter)]
  have hnum :
      ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) ≤
        ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter) := by
    linarith
  have hdiv :
      (ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)) /
          (ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)) ≤
        (ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter)) /
          (ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)) := by
    exact (div_le_div_iff_of_pos_right hden).2 hnum
  have hone :
      (ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)) /
          (ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)) = 1 := by
    exact div_self hden.ne'
  have hone' :
      (1 : ℝ) ≤
        (ctx.totalWeight + max ctx.alphaCenter (1 - ctx.alphaCenter)) /
          (ctx.totalWeight + (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2)) := by
    rwa [hone] at hdiv
  simpa [rawStepGain_eq (ctx := ctx), add_assoc] using hone'

end LocalContext

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

def StateBound
    (δ : ℝ)
    (state : PixelState κ) : Prop :=
  ∀ p, LocalContext.localInfinityNorm (state p) ≤ δ

noncomputable def rawOvershoot
    (data : CanonicalPixelData κ η)
    (state : PixelState κ)
    (p : κ) : ℝ :=
  LocalContext.localInfinityNorm (data.rawStep state p - clamp01 (data.rawStep state p))

def RawOvershootBound
    (data : CanonicalPixelData κ η)
    (σ : ℝ)
    (state : PixelState κ) : Prop :=
  ∀ p, rawOvershoot data state p ≤ σ

theorem stateClamp01_nonexpansive
    (state₁ state₂ : PixelState κ)
    (δ : ℝ)
    (hδ : StateBound δ (fun p => state₁ p - state₂ p)) :
    StateBound δ
      (fun p => CanonicalPixelData.stateClamp01 state₁ p -
        CanonicalPixelData.stateClamp01 state₂ p) := by
  intro p
  simpa [StateBound, CanonicalPixelData.stateClamp01, sub_eq_add_neg] using
    le_trans
      (LocalContext.clamp01_nonexpansive (g := state₁ p) (h := state₂ p))
      (hδ p)

end CanonicalPixelData

end FastMLFE2.Theory.Theorems
