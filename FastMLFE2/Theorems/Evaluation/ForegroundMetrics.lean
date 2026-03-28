import FastMLFE2.Evaluation.ForegroundMetrics
import FastMLFE2.Evaluation.AdversarialFamilies

namespace FastMLFE2.Theorems

open FastMLFE2.Evaluation
open FastMLFE2.Canonical

private theorem abs_sub_le_one_of_boxed
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a - b| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩

theorem rgbL1_nonneg (x : RGB) : 0 ≤ rgbL1 x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem rgbL2Sq_nonneg (x : RGB) : 0 ≤ rgbL2Sq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rgbL1_le_three_of_abs_le_one
    (x : RGB) (hx : ∀ c, |x c| ≤ 1) :
    rgbL1 x ≤ 3 := by
  simpa [rgbL1, Fin.sum_univ_three] using show |x 0| + |x 1| + |x 2| ≤ 3 by
    nlinarith [hx 0, hx 1, hx 2]

theorem rgbL2Sq_le_three_of_abs_le_one
    (x : RGB) (hx : ∀ c, |x c| ≤ 1) :
    rgbL2Sq x ≤ 3 := by
  have sq_le : ∀ c, x c ^ 2 ≤ 1 := fun c => by nlinarith [abs_le.mp (hx c)]
  simpa [rgbL2Sq, Fin.sum_univ_three] using show x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ 3 by
    nlinarith [sq_le 0, sq_le 1, sq_le 2]

theorem sad_nonneg
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w) :
    0 ≤ sad alpha estimated reference :=
  Finset.sum_nonneg fun _ hp =>
    mul_nonneg (le_of_lt (Finset.mem_filter.mp hp).2.1) (rgbL1_nonneg _)

theorem msePaper_nonneg
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w) :
    0 ≤ msePaper alpha estimated reference :=
  Finset.sum_nonneg fun _ hp =>
    mul_nonneg (le_of_lt (Finset.mem_filter.mp hp).2.1) (rgbL2Sq_nonneg _)

theorem sad_eq_zero_of_eq
    {h w : Nat} (alpha : GrayField h w) (img : RGBImage h w) :
    sad alpha img img = 0 := by simp

theorem msePaper_eq_zero_of_eq
    {h w : Nat} (alpha : GrayField h w) (img : RGBImage h w) :
    msePaper alpha img img = 0 := by simp

theorem sad_le_three_mul_alphaMass
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w)
    (hEst : ∀ p c, 0 ≤ estimated p c ∧ estimated p c ≤ 1)
    (hRef : ∀ p c, 0 ≤ reference p c ∧ reference p c ≤ 1) :
    sad alpha estimated reference ≤ 3 * alphaMass alpha := by
  calc sad alpha estimated reference
      ≤ (translucentSupport alpha).sum (fun p => alpha p * 3) :=
        Finset.sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_left
            (rgbL1_le_three_of_abs_le_one _ fun c => by
              simpa [rgbSub] using abs_sub_le_one_of_boxed (hEst p c).1 (hEst p c).2
                (hRef p c).1 (hRef p c).2)
            (le_of_lt (Finset.mem_filter.mp hp).2.1)
    _ = 3 * alphaMass alpha := by unfold alphaMass; rw [← Finset.sum_mul]; ring

theorem msePaper_le_three_mul_alphaMass
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w)
    (hEst : ∀ p c, 0 ≤ estimated p c ∧ estimated p c ≤ 1)
    (hRef : ∀ p c, 0 ≤ reference p c ∧ reference p c ≤ 1) :
    msePaper alpha estimated reference ≤ 3 * alphaMass alpha := by
  calc msePaper alpha estimated reference
      ≤ (translucentSupport alpha).sum (fun p => alpha p * 3) :=
        Finset.sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_left
            (rgbL2Sq_le_three_of_abs_le_one _ fun c => by
              simpa [rgbSub] using abs_sub_le_one_of_boxed (hEst p c).1 (hEst p c).2
                (hRef p c).1 (hRef p c).2)
            (le_of_lt (Finset.mem_filter.mp hp).2.1)
    _ = 3 * alphaMass alpha := by unfold alphaMass; rw [← Finset.sum_mul]; ring

theorem alphaMass_supportAlphaNearOpaque_eq
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    alphaMass (supportAlphaNearOpaque T ε) = (1 - ε) * T.card := by
  rw [alphaMass, translucentSupport_supportAlphaNearOpaque T hε0 hε1]
  have hsum : T.sum (fun x => supportAlphaNearOpaque T ε x) = T.sum (fun _ => (1 - ε)) :=
    Finset.sum_congr rfl fun x hx => by simp [supportAlphaNearOpaque, hx]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]; ring

theorem sad_supportAlphaNearOpaque_white_black_eq
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    sad (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
      (blackImage (h := h) (w := w)) = 3 * (1 - ε) * T.card := by
  rw [sad, translucentSupport_supportAlphaNearOpaque T hε0 hε1]
  have hsum : T.sum (fun x => supportAlphaNearOpaque T ε x *
      rgbL1 (rgbSub (whiteImage x) (blackImage x))) = T.sum (fun _ => (1 - ε) * 3) :=
    Finset.sum_congr rfl fun x hx => by
      simp [supportAlphaNearOpaque, rgbL1, rgbSub, whiteImage, blackImage, hx]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]; ring

theorem msePaper_supportAlphaNearOpaque_white_black_eq
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    msePaper (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
        (blackImage (h := h) (w := w)) = 3 * (1 - ε) * T.card := by
  rw [msePaper, translucentSupport_supportAlphaNearOpaque T hε0 hε1]
  have hsum : T.sum (fun x => supportAlphaNearOpaque T ε x *
      rgbL2Sq (rgbSub (whiteImage x) (blackImage x))) = T.sum (fun _ => (1 - ε) * 3) :=
    Finset.sum_congr rfl fun x hx => by
      simp [supportAlphaNearOpaque, rgbL2Sq, rgbSub, whiteImage, blackImage, hx]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]; ring

private theorem exists_near_opaque_gt_aux
    {h w : Nat} (T : Finset (Pixel h w)) (hT : T.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧ 3 * (1 - ε) * ↑T.card > 3 * ↑T.card - δ := by
  have hcard : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
  refine ⟨min (1 / 2) (δ / (6 * T.card)),
    by positivity,
    by linarith [min_le_left (1 / 2 : ℝ) (δ / (6 * T.card))], ?_⟩
  have hεle : min (1 / 2 : ℝ) (δ / (6 * T.card)) ≤ δ / (6 * T.card) := min_le_right _ _
  have : 3 * min (1 / 2 : ℝ) (δ / (6 * T.card)) * T.card ≤ δ / 2 := by
    calc 3 * min (1 / 2 : ℝ) (δ / (6 * T.card)) * T.card
        ≤ 3 * (δ / (6 * T.card)) * T.card := by nlinarith
      _ = δ / 2 := by field_simp; ring
  linarith

theorem exists_sad_supportAlphaNearOpaque_gt
    {h w : Nat} (T : Finset (Pixel h w)) (hT : T.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      3 * (T.card : ℝ) - δ <
        sad (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
          (blackImage (h := h) (w := w)) := by
  obtain ⟨ε, hε0, hε1, hgt⟩ := exists_near_opaque_gt_aux T hT hδ
  exact ⟨ε, hε0, hε1, by rw [sad_supportAlphaNearOpaque_white_black_eq T hε0 hε1]; linarith⟩

theorem exists_msePaper_supportAlphaNearOpaque_gt
    {h w : Nat} (T : Finset (Pixel h w)) (hT : T.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      3 * (T.card : ℝ) - δ <
        msePaper (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
          (blackImage (h := h) (w := w)) := by
  obtain ⟨ε, hε0, hε1, hgt⟩ := exists_near_opaque_gt_aux T hT hδ
  exact ⟨ε, hε0, hε1, by rw [msePaper_supportAlphaNearOpaque_white_black_eq T hε0 hε1]; linarith⟩

end FastMLFE2.Theorems
