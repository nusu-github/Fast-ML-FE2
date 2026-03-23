import FastMLFE2.Theory.Compositing.OneChannel

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Compositing

theorem abs_compose_sub_compose_le
    (alpha foreground background foreground' background' : ℝ) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      |alpha| * |foreground - foreground'| +
        |1 - alpha| * |background - background'| := by
  rw [compose_sub_compose]
  calc
    |alpha * (foreground - foreground') + (1 - alpha) * (background - background')|
      ≤ |alpha * (foreground - foreground')| + |(1 - alpha) * (background - background')| := by
        simpa using
          abs_add_le (alpha * (foreground - foreground')) ((1 - alpha) * (background - background'))
    _ = |alpha| * |foreground - foreground'| + |1 - alpha| * |background - background'| := by
      rw [abs_mul, abs_mul]

theorem abs_compose_sub_compose_le_authored
    {alpha foreground background foreground' background' : ℝ}
    (hα : 0 ≤ alpha)
    (hα' : alpha ≤ 1) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      alpha * |foreground - foreground'| +
        (1 - alpha) * |background - background'| := by
  have hbase := abs_compose_sub_compose_le alpha foreground background foreground' background'
  have habsα : |alpha| = alpha := abs_of_nonneg hα
  have habs1 : |1 - alpha| = 1 - alpha := abs_of_nonneg (sub_nonneg.mpr hα')
  rw [habsα, habs1] at hbase
  exact hbase

end FastMLFE2.Theory.Theorems
