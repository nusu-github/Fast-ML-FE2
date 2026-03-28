import FastMLFE2.Evaluation.DiscreteGradFamilies

namespace FastMLFE2.Theorems

open FastMLFE2.Evaluation
open scoped BigOperators

theorem defaultGaussianRaw_pos (t : Int) : 0 < defaultGaussianRaw t := by
  unfold defaultGaussianRaw defaultSigma
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.2
    positivity
  have hσ : 0 < ((7 : ℝ) / 5) := by norm_num
  have hden : 0 < ((7 : ℝ) / 5) * Real.sqrt (2 * Real.pi) := by
    exact mul_pos hσ hsqrt
  exact div_pos (Real.exp_pos _) hden

theorem defaultGaussianNormSq_pos : 0 < defaultGaussianNormSq := by
  unfold defaultGaussianNormSq
  have hmem : (0 : Int) ∈ defaultOffsets := by decide
  have hterm : 0 < defaultGaussianRaw 0 ^ 2 := by
    exact sq_pos_of_pos (defaultGaussianRaw_pos 0)
  refine lt_of_lt_of_le hterm ?_
  exact Finset.single_le_sum (fun _ _ => sq_nonneg _) hmem

theorem defaultGaussianNorm_pos : 0 < defaultGaussianNorm := by
  unfold defaultGaussianNorm
  exact Real.sqrt_pos.2 defaultGaussianNormSq_pos

theorem defaultGaussianDerivNormSq_pos : 0 < defaultGaussianDerivNormSq := by
  unfold defaultGaussianDerivNormSq
  have hmem : (1 : Int) ∈ defaultOffsets := by decide
  have hraw : defaultGaussianDerivRaw 1 ≠ 0 := by
    unfold defaultGaussianDerivRaw defaultSigma
    have hgauss : 0 < defaultGaussianRaw 1 := defaultGaussianRaw_pos 1
    have hfac : (-((((1 : Int) : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by norm_num
    exact ne_of_lt (mul_neg_of_neg_of_pos hfac hgauss)
  have hterm : 0 < defaultGaussianDerivRaw 1 ^ 2 := by
    exact sq_pos_iff.mpr hraw
  refine lt_of_lt_of_le hterm ?_
  exact Finset.single_le_sum (fun _ _ => sq_nonneg _) hmem

theorem defaultGaussianDerivNorm_pos : 0 < defaultGaussianDerivNorm := by
  unfold defaultGaussianDerivNorm
  exact Real.sqrt_pos.2 defaultGaussianDerivNormSq_pos

theorem defaultGaussianKernel_pos (t : Int) : 0 < defaultGaussianKernel t := by
  unfold defaultGaussianKernel
  exact div_pos (defaultGaussianRaw_pos t) defaultGaussianNorm_pos

theorem defaultGaussianDerivKernel_zero : defaultGaussianDerivKernel 0 = 0 := by
  unfold defaultGaussianDerivKernel defaultGaussianDerivRaw
  ring

theorem defaultGaussianDerivKernel_eq_neg (t : Int) :
    defaultGaussianDerivKernel (-t) = -defaultGaussianDerivKernel t := by
  unfold defaultGaussianDerivKernel defaultGaussianDerivRaw
  ring_nf
  simp [defaultGaussianRaw]
  ring

theorem defaultGaussianDerivMass_zero :
    defaultGaussianDerivMass = 0 := by
  unfold defaultGaussianDerivMass defaultOffsets
  rw [show ({-4, -3, -2, -1, 0, 1, 2, 3, 4} : Finset Int) =
      ({0, 1, -1, 2, -2, 3, -3, 4, -4} : Finset Int) by decide]
  simp [defaultGaussianDerivKernel_zero, defaultGaussianDerivKernel_eq_neg]

theorem gradientErrorDiscrete_nonneg
    {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (weights : GrayField h w) (mask : PixelMask h w)
    (estimated reference : RGBImage h w)
    (hweights : ∀ p ∈ mask, 0 ≤ weights p) :
    0 ≤ gradientErrorDiscrete weights mask estimated reference := by
  unfold gradientErrorDiscrete
  exact Finset.sum_nonneg (fun p hp =>
    mul_nonneg (hweights p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

noncomputable def centeredStepWitnessCoeff : ℝ :=
  defaultGaussianDerivKernel 1 + defaultGaussianDerivKernel 2 +
    defaultGaussianDerivKernel 3 + defaultGaussianDerivKernel 4

noncomputable def shiftedStepWitnessGap : ℝ :=
  -defaultGaussianDerivKernel 1

theorem centeredStepWitnessCoeff_lt_zero : centeredStepWitnessCoeff < 0 := by
  unfold centeredStepWitnessCoeff
  have h1 : defaultGaussianDerivKernel 1 < 0 := by
    unfold defaultGaussianDerivKernel defaultGaussianDerivRaw defaultSigma
    have hraw : defaultGaussianRaw 1 > 0 := defaultGaussianRaw_pos 1
    have hnorm : 0 < defaultGaussianDerivNorm := defaultGaussianDerivNorm_pos
    have hfac : (-((((1 : Int) : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by norm_num
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfac hraw) hnorm
  have h2 : defaultGaussianDerivKernel 2 < 0 := by
    unfold defaultGaussianDerivKernel defaultGaussianDerivRaw defaultSigma
    have hraw : defaultGaussianRaw 2 > 0 := defaultGaussianRaw_pos 2
    have hnorm : 0 < defaultGaussianDerivNorm := defaultGaussianDerivNorm_pos
    have hfac : (-((((2 : Int) : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by norm_num
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfac hraw) hnorm
  have h3 : defaultGaussianDerivKernel 3 < 0 := by
    unfold defaultGaussianDerivKernel defaultGaussianDerivRaw defaultSigma
    have hraw : defaultGaussianRaw 3 > 0 := defaultGaussianRaw_pos 3
    have hnorm : 0 < defaultGaussianDerivNorm := defaultGaussianDerivNorm_pos
    have hfac : (-((((3 : Int) : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by norm_num
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfac hraw) hnorm
  have h4 : defaultGaussianDerivKernel 4 < 0 := by
    unfold defaultGaussianDerivKernel defaultGaussianDerivRaw defaultSigma
    have hraw : defaultGaussianRaw 4 > 0 := defaultGaussianRaw_pos 4
    have hnorm : 0 < defaultGaussianDerivNorm := defaultGaussianDerivNorm_pos
    have hfac : (-((((4 : Int) : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by norm_num
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfac hraw) hnorm
  have hsum :
      defaultGaussianDerivKernel 1 + defaultGaussianDerivKernel 2 +
        defaultGaussianDerivKernel 3 + defaultGaussianDerivKernel 4 < 0 := by
    linarith
  simpa [centeredStepWitnessCoeff] using hsum

theorem shiftedStepWitnessGap_pos : 0 < shiftedStepWitnessGap := by
  unfold shiftedStepWitnessGap
  have h1 : defaultGaussianDerivKernel 1 < 0 := by
    unfold defaultGaussianDerivKernel defaultGaussianDerivRaw defaultSigma
    have hraw : defaultGaussianRaw 1 > 0 := defaultGaussianRaw_pos 1
    have hnorm : 0 < defaultGaussianDerivNorm := defaultGaussianDerivNorm_pos
    have hfac : (-((((1 : Int) : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by norm_num
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfac hraw) hnorm
  linarith

theorem centeredVerticalStep_distinct_from_flatBlack
    {h w : Nat} [Fact (8 < h)] [Fact (8 < w)] :
    centeredVerticalStepImage (h := h) (w := w) ≠ flatBlackImage := by
  intro hEq
  let p : FastMLFE2.Canonical.Pixel h w := (⟨8, Fact.out⟩, ⟨8, Fact.out⟩)
  have hval := congrFun (congrFun hEq p) 0
  simp [centeredVerticalStepImage, verticalStepImage, flatBlackImage, p] at hval

theorem shiftedVerticalStep_distinct_from_centered
    {h w : Nat} [Fact (8 < h)] [Fact (8 < w)] :
    shiftedVerticalStepImage (h := h) (w := w) ≠ centeredVerticalStepImage := by
  intro hEq
  let p : FastMLFE2.Canonical.Pixel h w := (⟨8, Fact.out⟩, ⟨8, Fact.out⟩)
  have hval := congrFun (congrFun hEq p) 0
  simp [shiftedVerticalStepImage, centeredVerticalStepImage, verticalStepImage, p] at hval

end FastMLFE2.Theorems
