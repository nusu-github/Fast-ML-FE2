import Mathlib

namespace FastMLFE2.Theory.Compositing

/-!
One-channel alpha compositing semantics over `ℝ`.
-/

/-- One-channel alpha compositing over `ℝ`. -/
def compose (alpha foreground background : ℝ) : ℝ :=
  alpha * foreground + (1 - alpha) * background

@[simp] theorem compose_zero_alpha (foreground background : ℝ) :
    compose 0 foreground background = background := by
  simp [compose]

@[simp] theorem compose_one_alpha (foreground background : ℝ) :
    compose 1 foreground background = foreground := by
  simp [compose]

theorem compose_sub_compose
    (alpha foreground background foreground' background' : ℝ) :
    compose alpha foreground background - compose alpha foreground' background' =
      alpha * (foreground - foreground') + (1 - alpha) * (background - background') := by
  simp [compose]
  ring

end FastMLFE2.Theory.Compositing
