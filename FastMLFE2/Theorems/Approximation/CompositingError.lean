import FastMLFE2.Compositing.OneChannel

namespace FastMLFE2.Theorems

open FastMLFE2.Compositing

theorem abs_compose_sub_compose_le
    (alpha foreground background foreground' background' : ℝ) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      |alpha| * |foreground - foreground'| + |1 - alpha| * |background - background'| := by
  rw [compose_sub_compose]; exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])

theorem abs_compose_sub_compose_le_authored
    {alpha foreground background foreground' background' : ℝ}
    (hα : 0 ≤ alpha) (hα' : alpha ≤ 1) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      alpha * |foreground - foreground'| + (1 - alpha) * |background - background'| := by
  have := abs_compose_sub_compose_le alpha foreground background foreground' background'
  rwa [abs_of_nonneg hα, abs_of_nonneg (sub_nonneg.mpr hα')] at this

end FastMLFE2.Theorems
