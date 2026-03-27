import FastMLFE2.Canonical.Grid
import Mathlib

namespace FastMLFE2.Evaluation

open FastMLFE2.Canonical

/-!
Finite-grid foreground metric semantics.

This module is the canonical home for paper `SAD`, paper-weighted `MSE`, and an abstract
finite-grid `GRAD` interface. The continuous Gaussian-window `GRAD` specialization lives in
`FastMLFE2.Evaluation.ContinuousGrad`.
-/

abbrev GrayField (h w : Nat) := Pixel h w → ℝ

abbrev RGB := Fin 3 → ℝ

abbrev RGBImage (h w : Nat) := Pixel h w → RGB

/-- The translucent region from the paper: pixels with `0 < α < 1`. -/
noncomputable def translucentSupport {h w : Nat} (alpha : GrayField h w) : Finset (Pixel h w) :=
  Finset.univ.filter fun p => 0 < alpha p ∧ alpha p < 1

/-- RGB channelwise difference. -/
def rgbSub (x y : RGB) : RGB :=
  fun c => x c - y c

/-- Channelwise `ℓ₁` norm on RGB. -/
def rgbL1 (x : RGB) : ℝ :=
  Finset.univ.sum fun c => |x c|

/-- Squared `ℓ₂` norm on RGB. -/
def rgbL2Sq (x : RGB) : ℝ :=
  Finset.univ.sum fun c => x c ^ 2

/-- Total translucent alpha mass. -/
noncomputable def alphaMass {h w : Nat} (alpha : GrayField h w) : ℝ :=
  (translucentSupport alpha).sum fun p => alpha p

/-- Paper SAD: weighted sum of absolute RGB differences over the translucent region. -/
noncomputable def sad {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w) :
    ℝ :=
  (translucentSupport alpha).sum fun p =>
    alpha p * rgbL1 (rgbSub (estimated p) (reference p))

/-- Paper MSE: weighted sum of squared RGB differences over the translucent region. -/
noncomputable def msePaper {h w : Nat} (alpha : GrayField h w)
    (estimated reference : RGBImage h w) : ℝ :=
  (translucentSupport alpha).sum fun p =>
    alpha p * rgbL2Sq (rgbSub (estimated p) (reference p))

/-- Abstract per-channel gradient-magnitude operator for later GRAD instantiation. -/
structure ChannelGradientOp (h w : Nat) where
  apply : GrayField h w → GrayField h w

/-- Paper GRAD specialized to an abstract gradient-magnitude operator. -/
noncomputable def gradMetric {h w : Nat} (op : ChannelGradientOp h w) (alpha : GrayField h w)
    (estimated reference : RGBImage h w) : ℝ :=
  (translucentSupport alpha).sum fun p =>
    alpha p *
      Finset.univ.sum fun c =>
        (op.apply (fun q => estimated q c) p - op.apply (fun q => reference q c) p) ^ 2

@[simp] theorem rgbSub_apply (x y : RGB) (c : Fin 3) :
    rgbSub x y c = x c - y c := rfl

@[simp] theorem rgbSub_self (x : RGB) : rgbSub x x = 0 := by
  funext c
  simp [rgbSub]

@[simp] theorem rgbL1_zero : rgbL1 0 = 0 := by
  simp [rgbL1]

@[simp] theorem rgbL2Sq_zero : rgbL2Sq 0 = 0 := by
  simp [rgbL2Sq]

@[simp] theorem sad_eq_zero_of_eq
    {h w : Nat} (alpha : GrayField h w) (img : RGBImage h w) :
    sad alpha img img = 0 := by
  simp [sad]

@[simp] theorem msePaper_eq_zero_of_eq
    {h w : Nat} (alpha : GrayField h w) (img : RGBImage h w) :
    msePaper alpha img img = 0 := by
  simp [msePaper]

@[simp] theorem gradMetric_eq_zero_of_eq
    {h w : Nat} (op : ChannelGradientOp h w) (alpha : GrayField h w) (img : RGBImage h w) :
    gradMetric op alpha img img = 0 := by
  simp [gradMetric]

end FastMLFE2.Evaluation
