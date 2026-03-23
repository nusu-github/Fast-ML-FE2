import FastMLFE2.Theory.Core.LocalEquation
import FastMLFE2.Theory.Theorems.ClosedForm

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core

namespace LocalContext

theorem clamp01Scalar_eq_self_of_mem_Icc
    {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    clamp01Scalar x = x := by
  simp [clamp01Scalar, hx0, hx1]

theorem clamp01_eq_self_of_bounds
    (g : LocalUnknown)
    (hfg0 : 0 ≤ foreground g)
    (hfg1 : foreground g ≤ 1)
    (hbg0 : 0 ≤ background g)
    (hbg1 : background g ≤ 1) :
    clamp01 g = g := by
  ext i
  fin_cases i
  · simp [clamp01, foreground, mkLocalUnknown]
    simpa [foreground] using
      clamp01Scalar_eq_self_of_mem_Icc (x := foreground g) hfg0 hfg1
  · simp [clamp01, background, mkLocalUnknown]
    simpa [background] using
      clamp01Scalar_eq_self_of_mem_Icc (x := background g) hbg0 hbg1

theorem clamp01_eq_self_iff
    (g : LocalUnknown) :
    clamp01 g = g ↔
      (0 ≤ foreground g ∧ foreground g ≤ 1) ∧
        (0 ≤ background g ∧ background g ≤ 1) := by
  constructor
  · intro h
    constructor
    · have hfg : clamp01Scalar (foreground g) = foreground g := by
        simpa [foreground_clamp01] using congrFun h 0
      constructor
      · by_cases hlt : foreground g < 0
        · have : clamp01Scalar (foreground g) = 0 := by
            simp [clamp01Scalar, le_of_lt hlt]
          linarith [hfg]
        · exact le_of_not_gt hlt
      · by_cases hlt : 1 < foreground g
        · have hmin : min 1 (foreground g) = 1 := by exact min_eq_left (le_of_lt hlt)
          have : clamp01Scalar (foreground g) = 1 := by
            simp [clamp01Scalar, hmin]
          linarith [hfg]
        · exact le_of_not_gt hlt
    · have hbg : clamp01Scalar (background g) = background g := by
        simpa [background_clamp01] using congrFun h 1
      constructor
      · by_cases hlt : background g < 0
        · have : clamp01Scalar (background g) = 0 := by
            simp [clamp01Scalar, le_of_lt hlt]
          linarith [hbg]
        · exact le_of_not_gt hlt
      · by_cases hlt : 1 < background g
        · have hmin : min 1 (background g) = 1 := by exact min_eq_left (le_of_lt hlt)
          have : clamp01Scalar (background g) = 1 := by
            simp [clamp01Scalar, hmin]
          linarith [hbg]
        · exact le_of_not_gt hlt
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
    clamp01 (closedFormSolution ctx) = closedFormSolution ctx := by
  exact clamp01_eq_self_of_bounds (closedFormSolution ctx) hfg0 hfg1 hbg0 hbg1

example (g : LocalUnknown) :
    clamp01 g = g ↔
      (0 ≤ foreground g ∧ foreground g ≤ 1) ∧
        (0 ≤ background g ∧ background g ≤ 1) := by
  simpa using clamp01_eq_self_iff (g := g)

end LocalContext

end FastMLFE2.Theory.Theorems
