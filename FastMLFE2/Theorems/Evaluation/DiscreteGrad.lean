import FastMLFE2.Evaluation.DiscreteGradFamilies

namespace FastMLFE2.Theorems

open FastMLFE2.Evaluation
open scoped BigOperators

theorem defaultGaussianRaw_pos (t : Int) : 0 < defaultGaussianRaw t := by
  unfold defaultGaussianRaw defaultSigma
  exact div_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.sqrt_pos.2 (by positivity)))

theorem defaultGaussianNormSq_pos : 0 < defaultGaussianNormSq := by
  unfold defaultGaussianNormSq
  exact lt_of_lt_of_le (sq_pos_of_pos (defaultGaussianRaw_pos 0))
    (Finset.single_le_sum (fun _ _ => sq_nonneg _) (show (0 : Int) ∈ defaultOffsets by decide))

theorem defaultGaussianNorm_pos : 0 < defaultGaussianNorm :=
  Real.sqrt_pos.2 defaultGaussianNormSq_pos

theorem defaultGaussianDerivNormSq_pos : 0 < defaultGaussianDerivNormSq := by
  unfold defaultGaussianDerivNormSq
  have hraw : defaultGaussianDerivRaw 1 ≠ 0 := by
    unfold defaultGaussianDerivRaw defaultSigma
    exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) (defaultGaussianRaw_pos 1))
  exact lt_of_lt_of_le (sq_pos_iff.mpr hraw)
    (Finset.single_le_sum (fun _ _ => sq_nonneg _) (show (1 : Int) ∈ defaultOffsets by decide))

theorem defaultGaussianDerivNorm_pos : 0 < defaultGaussianDerivNorm :=
  Real.sqrt_pos.2 defaultGaussianDerivNormSq_pos

theorem defaultGaussianKernel_pos (t : Int) : 0 < defaultGaussianKernel t :=
  div_pos (defaultGaussianRaw_pos t) defaultGaussianNorm_pos

theorem defaultGaussianDerivKernel_zero : defaultGaussianDerivKernel 0 = 0 := by
  unfold defaultGaussianDerivKernel defaultGaussianDerivRaw; ring

theorem defaultGaussianDerivKernel_eq_neg (t : Int) :
    defaultGaussianDerivKernel (-t) = -defaultGaussianDerivKernel t := by
  unfold defaultGaussianDerivKernel defaultGaussianDerivRaw
  ring_nf; simp [defaultGaussianRaw]; ring

theorem defaultGaussianDerivMass_zero :
    defaultGaussianDerivMass = 0 := by
  unfold defaultGaussianDerivMass defaultOffsets
  rw [show ({-4, -3, -2, -1, 0, 1, 2, 3, 4} : Finset Int) =
      ({0, 1, -1, 2, -2, 3, -3, 4, -4} : Finset Int) by decide]
  simp [defaultGaussianDerivKernel_zero, defaultGaussianDerivKernel_eq_neg]

private theorem defaultGaussianDerivKernel_neg_of_pos (k : Int) (hk : 0 < k) :
    defaultGaussianDerivKernel k < 0 := by
  unfold defaultGaussianDerivKernel defaultGaussianDerivRaw defaultSigma
  have hfac : (-(((k : ℝ) / (((7 : ℝ) / 5) ^ 2))) : ℝ) < 0 := by
    have : (0 : ℝ) < k := Int.cast_pos.mpr hk; norm_num; linarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfac (defaultGaussianRaw_pos k))
    defaultGaussianDerivNorm_pos

theorem gradientErrorDiscrete_nonneg
    {h w : Nat} [Fact (0 < h)] [Fact (0 < w)]
    (weights : GrayField h w) (mask : PixelMask h w)
    (estimated reference : RGBImage h w)
    (hweights : ∀ p ∈ mask, 0 ≤ weights p) :
    0 ≤ gradientErrorDiscrete weights mask estimated reference :=
  Finset.sum_nonneg fun p hp =>
    mul_nonneg (hweights p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

noncomputable def centeredStepWitnessCoeff : ℝ :=
  defaultGaussianDerivKernel 1 + defaultGaussianDerivKernel 2 +
    defaultGaussianDerivKernel 3 + defaultGaussianDerivKernel 4

noncomputable def shiftedStepWitnessGap : ℝ :=
  -defaultGaussianDerivKernel 1

theorem centeredStepWitnessCoeff_lt_zero : centeredStepWitnessCoeff < 0 := by
  unfold centeredStepWitnessCoeff
  linarith [defaultGaussianDerivKernel_neg_of_pos 1 (by norm_num),
    defaultGaussianDerivKernel_neg_of_pos 2 (by norm_num),
    defaultGaussianDerivKernel_neg_of_pos 3 (by norm_num),
    defaultGaussianDerivKernel_neg_of_pos 4 (by norm_num)]

theorem shiftedStepWitnessGap_pos : 0 < shiftedStepWitnessGap := by
  unfold shiftedStepWitnessGap
  linarith [defaultGaussianDerivKernel_neg_of_pos 1 (by norm_num)]

theorem centeredVerticalStep_distinct_from_flatBlack
    {h w : Nat} [Fact (8 < h)] [Fact (8 < w)] :
    centeredVerticalStepImage (h := h) (w := w) ≠ flatBlackImage := by
  intro hEq
  have := congrFun (congrFun hEq (⟨8, Fact.out⟩, ⟨8, Fact.out⟩)) 0
  simp [centeredVerticalStepImage, verticalStepImage, flatBlackImage] at this

theorem shiftedVerticalStep_distinct_from_centered
    {h w : Nat} [Fact (8 < h)] [Fact (8 < w)] :
    shiftedVerticalStepImage (h := h) (w := w) ≠ centeredVerticalStepImage := by
  intro hEq
  have := congrFun (congrFun hEq (⟨8, Fact.out⟩, ⟨8, Fact.out⟩)) 0
  simp [shiftedVerticalStepImage, centeredVerticalStepImage, verticalStepImage] at this

end FastMLFE2.Theorems
