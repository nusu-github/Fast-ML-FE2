import FastMLFE2.Core.LocalEquation
import FastMLFE2.Theorems.ClosedForm

namespace FastMLFE2.Theorems

open FastMLFE2.Core

namespace LocalContext

theorem clamp01Scalar_eq_self_of_mem_Icc
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    clamp01Scalar x = x := by
  simp [clamp01Scalar, hx0, hx1]

theorem clamp01_eq_self_of_bounds
    (g : LocalUnknown)
    (hfg0 : 0 ≤ foreground g) (hfg1 : foreground g ≤ 1)
    (hbg0 : 0 ≤ background g) (hbg1 : background g ≤ 1) :
    clamp01 g = g := by
  ext i; fin_cases i
  · simpa [clamp01, foreground, mkLocalUnknown] using
      clamp01Scalar_eq_self_of_mem_Icc hfg0 hfg1
  · simpa [clamp01, background, mkLocalUnknown] using
      clamp01Scalar_eq_self_of_mem_Icc hbg0 hbg1

private theorem bounds_of_clamp01Scalar_eq_self {x : ℝ} (h : clamp01Scalar x = x) :
    0 ≤ x ∧ x ≤ 1 := by
  constructor
  · by_contra hlt
    have : clamp01Scalar x = 0 := by simp [clamp01Scalar, le_of_not_ge hlt]
    linarith
  · by_contra hlt
    have : clamp01Scalar x = 1 := by
      simp [clamp01Scalar, min_eq_left (le_of_lt (lt_of_not_ge hlt))]
    linarith

theorem clamp01_eq_self_iff (g : LocalUnknown) :
    clamp01 g = g ↔
      (0 ≤ foreground g ∧ foreground g ≤ 1) ∧
        (0 ≤ background g ∧ background g ≤ 1) := by
  constructor
  · intro h
    have hfg : clamp01Scalar (foreground g) = foreground g := by
      simpa [foreground_clamp01] using congrFun h 0
    have hbg : clamp01Scalar (background g) = background g := by
      simpa [background_clamp01] using congrFun h 1
    exact ⟨bounds_of_clamp01Scalar_eq_self hfg, bounds_of_clamp01Scalar_eq_self hbg⟩
  · rintro ⟨⟨hfg0, hfg1⟩, ⟨hbg0, hbg1⟩⟩
    exact clamp01_eq_self_of_bounds g hfg0 hfg1 hbg0 hbg1

theorem closedForm_clamp01_eq_self_of_component_bounds
    {ι : Type*} [Fintype ι]
    (ctx : LocalContext ι)
    [Assumptions.CoreMathAssumptions ctx]
    (hfg0 : 0 ≤ foreground (closedFormSolution ctx))
    (hfg1 : foreground (closedFormSolution ctx) ≤ 1)
    (hbg0 : 0 ≤ background (closedFormSolution ctx))
    (hbg1 : background (closedFormSolution ctx) ≤ 1) :
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx :=
  clamp01_eq_self_of_bounds _ hfg0 hfg1 hbg0 hbg1

example (g : LocalUnknown) :
    clamp01 g = g ↔
      (0 ≤ foreground g ∧ foreground g ≤ 1) ∧
        (0 ≤ background g ∧ background g ≤ 1) :=
  clamp01_eq_self_iff g

end LocalContext

end FastMLFE2.Theorems
