import FastMLFE2.Notation

namespace FastMLFE2

/-- The left-hand side `α F + (1 - α) B` of the compositing equation. -/
def compositingValue (α : ℝ) (g : FBVec) : ℝ :=
  dotProduct (uVec α) g

def compositingResidual (α image : ℝ) (g : FBVec) : ℝ :=
  compositingValue α g - image

theorem compositingValue_eq (α : ℝ) (g : FBVec) :
    compositingValue α g = α * foreground g + (1 - α) * background g := by
  simp [compositingValue, uVec, foreground, background, dotProduct, Fin.sum_univ_two]

theorem compositingResidual_eq (α image : ℝ) (g : FBVec) :
    compositingResidual α image g =
      α * foreground g + (1 - α) * background g - image := by
  simp [compositingResidual, compositingValue_eq]

end FastMLFE2
