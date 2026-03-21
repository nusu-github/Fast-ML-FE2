import FastMLFE2.NormalEquation

namespace FastMLFE2

namespace LocalData

variable {ι : Type*} [Fintype ι]

theorem systemMatrix_det (data : LocalData ι) (α : ℝ) :
    (data.systemMatrix α).det =
      data.totalWeight * (data.totalWeight + α ^ 2 + (1 - α) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [systemMatrix]
  ring

theorem systemMatrix_det_pos_of_totalWeight_pos (data : LocalData ι) {α : ℝ}
    (h : 0 < data.totalWeight) :
    0 < (data.systemMatrix α).det := by
  rw [systemMatrix_det]
  have hsquares : 0 ≤ α ^ 2 + (1 - α) ^ 2 := by positivity
  nlinarith

def summaryDenom (data : LocalData ι) (α : ℝ) : ℝ :=
  data.totalWeight * (data.totalWeight + α ^ 2 + (1 - α) ^ 2)

abbrev closedFormDenom (data : LocalData ι) (α : ℝ) : ℝ :=
  data.summaryDenom α

theorem closedFormDenom_eq_det (data : LocalData ι) (α : ℝ) :
    data.closedFormDenom α = (data.systemMatrix α).det := by
  simpa [summaryDenom] using (data.systemMatrix_det α).symm

/-- Explicit `2 × 2` closed form, i.e. the concrete instance of `(U Uᵀ + Rᵀ V R)⁻¹ (...)`. -/
noncomputable def closedForm (data : LocalData ι) (α image : ℝ) : FBVec :=
  let s := data.totalWeight
  let b := data.rhs α image
  let det := data.closedFormDenom α
  ![
    (((1 - α) ^ 2 + s) * foreground b - α * (1 - α) * background b) / det,
    ((α ^ 2 + s) * background b - α * (1 - α) * foreground b) / det
  ]

theorem closedForm_solves_localSystem (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.localSystem α image (data.closedForm α image) := by
  have hdetPos : 0 < data.closedFormDenom α := by
    have hsquares : 0 ≤ α ^ 2 + (1 - α) ^ 2 := by positivity
    have hsum : 0 < data.totalWeight + α ^ 2 + (1 - α) ^ 2 := by
      nlinarith
    have : 0 < data.totalWeight * (data.totalWeight + α ^ 2 + (1 - α) ^ 2) := by
      positivity
    simpa [closedFormDenom] using this
  have hdet : data.closedFormDenom α ≠ 0 := by
    linarith
  ext i
  fin_cases i
  · simp [closedForm, closedFormDenom, foreground, background, systemMatrix,
      rhs, foregroundSum, backgroundSum, summaryDenom, Matrix.mulVec]
    field_simp [hdet]
    ring_nf
  · simp [closedForm, closedFormDenom, foreground, background, systemMatrix,
      rhs, foregroundSum, backgroundSum, summaryDenom, Matrix.mulVec]
    field_simp [hdet]
    ring_nf

theorem closedForm_stationary (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.stationary α image (data.closedForm α image) := by
  rw [stationary_iff_localSystem]
  exact data.closedForm_solves_localSystem α image h

end LocalData

end FastMLFE2
