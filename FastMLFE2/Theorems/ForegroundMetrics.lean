import FastMLFE2.Evaluation.ForegroundMetrics
import FastMLFE2.Evaluation.AdversarialFamilies

namespace FastMLFE2.Theorems

open FastMLFE2.Evaluation
open FastMLFE2.Canonical

private theorem abs_sub_le_one_of_boxed
    {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a - b| ≤ 1 := by
  refine abs_le.2 ?_
  constructor <;> linarith

theorem rgbL1_nonneg (x : RGB) : 0 ≤ rgbL1 x := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem rgbL2Sq_nonneg (x : RGB) : 0 ≤ rgbL2Sq x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem rgbL1_le_three_of_abs_le_one
    (x : RGB) (hx : ∀ c, |x c| ≤ 1) :
    rgbL1 x ≤ 3 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have hs : |x 0| + |x 1| + |x 2| ≤ 3 := by
    nlinarith
  simpa [rgbL1, Fin.sum_univ_three] using hs

theorem rgbL2Sq_le_three_of_abs_le_one
    (x : RGB) (hx : ∀ c, |x c| ≤ 1) :
    rgbL2Sq x ≤ 3 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h0sq : x 0 ^ 2 ≤ 1 := by
    rcases abs_le.mp h0 with ⟨h0l, h0u⟩
    nlinarith
  have h1sq : x 1 ^ 2 ≤ 1 := by
    rcases abs_le.mp h1 with ⟨h1l, h1u⟩
    nlinarith
  have h2sq : x 2 ^ 2 ≤ 1 := by
    rcases abs_le.mp h2 with ⟨h2l, h2u⟩
    nlinarith
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ 3 := by
    nlinarith
  simpa [rgbL2Sq, Fin.sum_univ_three] using hs

theorem sad_nonneg
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w) :
    0 ≤ sad alpha estimated reference := by
  unfold sad
  refine Finset.sum_nonneg ?_
  intro p hp
  have hα : 0 ≤ alpha p := le_of_lt ((Finset.mem_filter.mp hp).2.1)
  have hnorm : 0 ≤ rgbL1 (rgbSub (estimated p) (reference p)) :=
    rgbL1_nonneg _
  nlinarith

theorem msePaper_nonneg
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w) :
    0 ≤ msePaper alpha estimated reference := by
  unfold msePaper
  refine Finset.sum_nonneg ?_
  intro p hp
  have hα : 0 ≤ alpha p := le_of_lt ((Finset.mem_filter.mp hp).2.1)
  have hnorm : 0 ≤ rgbL2Sq (rgbSub (estimated p) (reference p)) :=
    rgbL2Sq_nonneg _
  nlinarith

theorem sad_eq_zero_of_eq
    {h w : Nat} (alpha : GrayField h w) (img : RGBImage h w) :
    sad alpha img img = 0 := by
  simp

theorem msePaper_eq_zero_of_eq
    {h w : Nat} (alpha : GrayField h w) (img : RGBImage h w) :
    msePaper alpha img img = 0 := by
  simp

theorem sad_le_three_mul_alphaMass
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w)
    (hEst : ∀ p c, 0 ≤ estimated p c ∧ estimated p c ≤ 1)
    (hRef : ∀ p c, 0 ≤ reference p c ∧ reference p c ≤ 1) :
    sad alpha estimated reference ≤ 3 * alphaMass alpha := by
  calc
    sad alpha estimated reference
      = (translucentSupport alpha).sum
          (fun p => alpha p * rgbL1 (rgbSub (estimated p) (reference p))) := rfl
    _ ≤ (translucentSupport alpha).sum (fun p => alpha p * 3) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      have hα : 0 ≤ alpha p := le_of_lt ((Finset.mem_filter.mp hp).2.1)
      have hnorm : rgbL1 (rgbSub (estimated p) (reference p)) ≤ 3 := by
        refine rgbL1_le_three_of_abs_le_one _ ?_
        intro c
        rcases hEst p c with ⟨he0, he1⟩
        rcases hRef p c with ⟨hr0, hr1⟩
        simpa [rgbSub] using abs_sub_le_one_of_boxed he0 he1 hr0 hr1
      exact mul_le_mul_of_nonneg_left hnorm hα
    _ = 3 * alphaMass alpha := by
      unfold alphaMass
      rw [← Finset.sum_mul]
      ring

theorem msePaper_le_three_mul_alphaMass
    {h w : Nat} (alpha : GrayField h w) (estimated reference : RGBImage h w)
    (hEst : ∀ p c, 0 ≤ estimated p c ∧ estimated p c ≤ 1)
    (hRef : ∀ p c, 0 ≤ reference p c ∧ reference p c ≤ 1) :
    msePaper alpha estimated reference ≤ 3 * alphaMass alpha := by
  calc
    msePaper alpha estimated reference
      = (translucentSupport alpha).sum
          (fun p => alpha p * rgbL2Sq (rgbSub (estimated p) (reference p))) := rfl
    _ ≤ (translucentSupport alpha).sum (fun p => alpha p * 3) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      have hα : 0 ≤ alpha p := le_of_lt ((Finset.mem_filter.mp hp).2.1)
      have hnorm : rgbL2Sq (rgbSub (estimated p) (reference p)) ≤ 3 := by
        refine rgbL2Sq_le_three_of_abs_le_one _ ?_
        intro c
        rcases hEst p c with ⟨he0, he1⟩
        rcases hRef p c with ⟨hr0, hr1⟩
        simpa [rgbSub] using abs_sub_le_one_of_boxed he0 he1 hr0 hr1
      exact mul_le_mul_of_nonneg_left hnorm hα
    _ = 3 * alphaMass alpha := by
      unfold alphaMass
      rw [← Finset.sum_mul]
      ring

theorem alphaMass_supportAlphaNearOpaque_eq
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    alphaMass (supportAlphaNearOpaque T ε) = (1 - ε) * T.card := by
  rw [alphaMass, translucentSupport_supportAlphaNearOpaque T hε0 hε1]
  have hsum :
      T.sum (fun x => supportAlphaNearOpaque T ε x) = T.sum (fun _x => (1 - ε)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [supportAlphaNearOpaque, hx]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sad_supportAlphaNearOpaque_white_black_eq
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    sad (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w)) (blackImage (h := h) (w := w)) =
      3 * (1 - ε) * T.card := by
  rw [sad, translucentSupport_supportAlphaNearOpaque T hε0 hε1]
  have hsum :
      T.sum (fun x =>
          supportAlphaNearOpaque T ε x *
            rgbL1 (rgbSub (whiteImage (h := h) (w := w) x) (blackImage (h := h) (w := w) x))) =
        T.sum (fun _x => (1 - ε) * 3) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [supportAlphaNearOpaque, rgbL1, rgbSub, whiteImage, blackImage, hx]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem msePaper_supportAlphaNearOpaque_white_black_eq
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    msePaper (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
        (blackImage (h := h) (w := w)) =
      3 * (1 - ε) * T.card := by
  rw [msePaper, translucentSupport_supportAlphaNearOpaque T hε0 hε1]
  have hsum :
      T.sum (fun x =>
          supportAlphaNearOpaque T ε x *
            rgbL2Sq (rgbSub (whiteImage (h := h) (w := w) x) (blackImage (h := h) (w := w) x))) =
        T.sum (fun _x => (1 - ε) * 3) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [supportAlphaNearOpaque, rgbL2Sq, rgbSub, whiteImage, blackImage, hx]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  ring

theorem exists_sad_supportAlphaNearOpaque_gt
    {h w : Nat} (T : Finset (Pixel h w)) (hT : T.Nonempty) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      3 * (T.card : ℝ) - δ <
        sad (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
          (blackImage (h := h) (w := w)) := by
  let ε : ℝ := min ((1 : ℝ) / 2) (δ / (6 * T.card))
  have hcard : 0 < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hε0 : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · norm_num
    · positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    have hhalf : min ((1 : ℝ) / 2) (δ / (6 * T.card)) ≤ (1 : ℝ) / 2 := min_le_left _ _
    linarith
  refine ⟨ε, hε0, hε1, ?_⟩
  rw [sad_supportAlphaNearOpaque_white_black_eq T hε0 hε1]
  have hεle : ε ≤ δ / (6 * T.card) := by
    dsimp [ε]
    exact min_le_right _ _
  have hcard_ne : (T.card : ℝ) ≠ 0 := ne_of_gt hcard
  have hbound :
      3 * ε * (T.card : ℝ) < δ := by
    have hstep : 3 * ε * (T.card : ℝ) ≤ 3 * (δ / (6 * T.card)) * (T.card : ℝ) := by
      gcongr
    have hEq : 3 * (δ / (6 * T.card)) * (T.card : ℝ) = δ / 2 := by
      field_simp [hcard_ne]
      ring
    have hhalfδ : δ / 2 < δ := by linarith
    exact lt_of_le_of_lt (by simpa [hEq] using hstep) hhalfδ
  nlinarith

theorem exists_msePaper_supportAlphaNearOpaque_gt
    {h w : Nat} (T : Finset (Pixel h w)) (hT : T.Nonempty) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      3 * (T.card : ℝ) - δ <
        msePaper (supportAlphaNearOpaque T ε) (whiteImage (h := h) (w := w))
          (blackImage (h := h) (w := w)) := by
  let ε : ℝ := min ((1 : ℝ) / 2) (δ / (6 * T.card))
  have hcard : 0 < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hε0 : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · norm_num
    · positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    have hhalf : min ((1 : ℝ) / 2) (δ / (6 * T.card)) ≤ (1 : ℝ) / 2 := min_le_left _ _
    linarith
  refine ⟨ε, hε0, hε1, ?_⟩
  rw [msePaper_supportAlphaNearOpaque_white_black_eq T hε0 hε1]
  have hεle : ε ≤ δ / (6 * T.card) := by
    dsimp [ε]
    exact min_le_right _ _
  have hcard_ne : (T.card : ℝ) ≠ 0 := ne_of_gt hcard
  have hbound :
      3 * ε * (T.card : ℝ) < δ := by
    have hstep : 3 * ε * (T.card : ℝ) ≤ 3 * (δ / (6 * T.card)) * (T.card : ℝ) := by
      gcongr
    have hEq : 3 * (δ / (6 * T.card)) * (T.card : ℝ) = δ / 2 := by
      field_simp [hcard_ne]
      ring
    have hhalfδ : δ / 2 < δ := by linarith
    exact lt_of_le_of_lt (by simpa [hEq] using hstep) hhalfδ
  nlinarith

end FastMLFE2.Theorems
