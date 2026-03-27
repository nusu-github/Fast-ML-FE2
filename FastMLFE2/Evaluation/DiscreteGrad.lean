import FastMLFE2.Evaluation.ForegroundMetrics
import Mathlib

namespace FastMLFE2.Evaluation

open FastMLFE2.Canonical
open scoped BigOperators

/-!
Discrete Gaussian-gradient semantics matching the Python evaluation kernel at its default
configuration `sigma = 1.4`.

This module models the `metrics.py` implementation directly:

* odd-width support `{-4, …, 4}` coming from `floor (3 * 1.4) = 4`
* sampled 1D Gaussian and its derivative
* per-kernel `ℓ₂` normalization
* separable correlation with SciPy-style `mode = "reflect"` and `origin = 0`
-/

abbrev GrayImage (h w : Nat) := Pixel h w → ℝ

abbrev PixelMask (h w : Nat) := Finset (Pixel h w)

noncomputable def defaultSigma : ℝ :=
  (7 : ℝ) / 5

def defaultOffsets : Finset Int :=
  ({-4, -3, -2, -1, 0, 1, 2, 3, 4} : Finset Int)

def positiveDefaultOffsets : Finset Int :=
  ({1, 2, 3, 4} : Finset Int)

noncomputable def defaultGaussianRaw (t : Int) : ℝ :=
  Real.exp (-((((t : ℝ) ^ 2) / (2 * defaultSigma ^ 2)))) /
    (defaultSigma * Real.sqrt (2 * Real.pi))

noncomputable def defaultGaussianDerivRaw (t : Int) : ℝ :=
  (-((t : ℝ) / (defaultSigma ^ 2))) * defaultGaussianRaw t

noncomputable def defaultGaussianNormSq : ℝ :=
  Finset.sum defaultOffsets fun t => defaultGaussianRaw t ^ 2

noncomputable def defaultGaussianDerivNormSq : ℝ :=
  Finset.sum defaultOffsets fun t => defaultGaussianDerivRaw t ^ 2

noncomputable def defaultGaussianNorm : ℝ :=
  Real.sqrt defaultGaussianNormSq

noncomputable def defaultGaussianDerivNorm : ℝ :=
  Real.sqrt defaultGaussianDerivNormSq

noncomputable def defaultGaussianKernel (t : Int) : ℝ :=
  defaultGaussianRaw t / defaultGaussianNorm

noncomputable def defaultGaussianDerivKernel (t : Int) : ℝ :=
  defaultGaussianDerivRaw t / defaultGaussianDerivNorm

noncomputable def defaultGaussianMass : ℝ :=
  Finset.sum defaultOffsets defaultGaussianKernel

noncomputable def defaultGaussianDerivMass : ℝ :=
  Finset.sum defaultOffsets defaultGaussianDerivKernel

def reflectNat (n : Nat) (i : Int) : Nat :=
  if h : n ≤ 1 then
    0
  else
    let period := 2 * n - 2
    let j := Int.toNat (i.emod period)
    if hj : j < n then j else period - j

theorem reflectNat_lt (n : Nat) (hn : 0 < n) (i : Int) :
    reflectNat n i < n := by
  by_cases hsmall : n ≤ 1
  · have hn1 : n = 1 := by omega
    simp [reflectNat, hsmall, hn1]
  · simp [reflectNat, hsmall]
    set period := 2 * n - 2
    set j : Nat := Int.toNat (i.emod period)
    have hperiod : 0 < period := by
      dsimp [period]
      omega
    have hjperiod : j < period := by
      dsimp [j]
      have hnonneg : 0 ≤ i.emod period := Int.emod_nonneg _ (by exact_mod_cast hperiod.ne')
      have hlt : i.emod period < period := Int.emod_lt_of_pos _ (by exact_mod_cast hperiod)
      have hltInt : ((Int.toNat (i.emod period) : Nat) : Int) < period := by
        rw [Int.toNat_of_nonneg hnonneg]
        exact hlt
      exact Int.ofNat_lt.mp hltInt
    split
    · assumption
    · omega

def reflectFin (n : Nat) [Fact (0 < n)] (i : Int) : Fin n :=
  ⟨reflectNat n i, reflectNat_lt n Fact.out i⟩

noncomputable def correlateHorizontal {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (kernel : Int → ℝ) (img : GrayImage h w) (p : Pixel h w) : ℝ :=
  Finset.sum defaultOffsets fun t => kernel t * img (p.1, reflectFin w ((p.2.1 : Int) + t))

noncomputable def correlateVertical {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (kernel : Int → ℝ) (img : GrayImage h w) (p : Pixel h w) : ℝ :=
  Finset.sum defaultOffsets fun t => kernel t * img (reflectFin h ((p.1.1 : Int) + t), p.2)

noncomputable def defaultGaussianDx {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (img : GrayImage h w) (p : Pixel h w) : ℝ :=
  correlateVertical defaultGaussianKernel
    (fun q => correlateHorizontal defaultGaussianDerivKernel img q) p

noncomputable def defaultGaussianDy {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (img : GrayImage h w) (p : Pixel h w) : ℝ :=
  correlateHorizontal defaultGaussianKernel
    (fun q => correlateVertical defaultGaussianDerivKernel img q) p

noncomputable def defaultGradientMagnitudeChannel {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (img : GrayImage h w) (p : Pixel h w) : ℝ :=
  Real.sqrt (defaultGaussianDx img p ^ 2 + defaultGaussianDy img p ^ 2)

noncomputable def gradientErrorDiscrete
    {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (weights : GrayField h w) (mask : PixelMask h w)
    (estimated reference : RGBImage h w) : ℝ :=
  Finset.sum mask fun p =>
    weights p *
      Finset.sum Finset.univ fun c : Fin 3 =>
        (defaultGradientMagnitudeChannel (fun q => estimated q c) p -
          defaultGradientMagnitudeChannel (fun q => reference q c) p) ^ 2

noncomputable def gradientErrorTranslucent
    {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (alpha : GrayField h w) (estimated reference : RGBImage h w) : ℝ :=
  gradientErrorDiscrete alpha (translucentSupport alpha) estimated reference

@[simp] theorem gradientErrorDiscrete_eq_zero_of_eq
    {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (weights : GrayField h w) (mask : PixelMask h w) (img : RGBImage h w) :
    gradientErrorDiscrete weights mask img img = 0 := by
  unfold gradientErrorDiscrete
  simp

@[simp] theorem gradientErrorTranslucent_eq_zero_of_eq
    {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (alpha : GrayField h w) (img : RGBImage h w) :
    gradientErrorTranslucent alpha img img = 0 := by
  simp [gradientErrorTranslucent]

end FastMLFE2.Evaluation
