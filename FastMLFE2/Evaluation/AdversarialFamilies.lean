import FastMLFE2.Evaluation.ForegroundMetrics

namespace FastMLFE2.Evaluation

open FastMLFE2.Canonical

/-- Constant black RGB image. -/
def blackImage {h w : Nat} : RGBImage h w :=
  fun _ _ => 0

/-- Constant white RGB image. -/
def whiteImage {h w : Nat} : RGBImage h w :=
  fun _ _ => 1

/-- Alpha family equal to `1 - ε` on the target support and `1` elsewhere. -/
def supportAlphaNearOpaque {h w : Nat} (T : Finset (Pixel h w)) (ε : ℝ) : GrayField h w :=
  fun p => if p ∈ T then 1 - ε else 1

@[simp] theorem blackImage_apply {h w : Nat} (p : Pixel h w) (c : Fin 3) :
    blackImage (h := h) (w := w) p c = 0 := rfl

@[simp] theorem whiteImage_apply {h w : Nat} (p : Pixel h w) (c : Fin 3) :
    whiteImage (h := h) (w := w) p c = 1 := rfl

@[simp] theorem supportAlphaNearOpaque_of_mem
    {h w : Nat} {T : Finset (Pixel h w)} {ε : ℝ} {p : Pixel h w}
    (hp : p ∈ T) :
    supportAlphaNearOpaque T ε p = 1 - ε := by
  simp [supportAlphaNearOpaque, hp]

@[simp] theorem supportAlphaNearOpaque_of_not_mem
    {h w : Nat} {T : Finset (Pixel h w)} {ε : ℝ} {p : Pixel h w}
    (hp : p ∉ T) :
    supportAlphaNearOpaque T ε p = 1 := by
  simp [supportAlphaNearOpaque, hp]

theorem translucentSupport_supportAlphaNearOpaque
    {h w : Nat} (T : Finset (Pixel h w)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    translucentSupport (supportAlphaNearOpaque T ε) = T := by
  classical
  ext p
  by_cases hp : p ∈ T
  · have hα : 0 < 1 - ε ∧ 1 - ε < 1 := by
      constructor <;> linarith
    simp [translucentSupport, supportAlphaNearOpaque, hp, hα]
  · have hα : ¬ (0 < (1 : ℝ) ∧ (1 : ℝ) < 1) := by
      simp
    simp [translucentSupport, supportAlphaNearOpaque, hp]

end FastMLFE2.Evaluation
