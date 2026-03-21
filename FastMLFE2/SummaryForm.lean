import FastMLFE2.LocalSolver

namespace FastMLFE2

namespace LocalData

variable {ι : Type*} [Fintype ι]

/-- The summary-form foreground update depending only on `α`, `I`, `s`, `p_F`, `p_B`, and `d`. -/
noncomputable def summaryForeground (data : LocalData ι) (α image : ℝ) : ℝ :=
  let s := data.totalWeight
  let pF := data.foregroundSum
  let pB := data.backgroundSum
  let d := data.summaryDenom α
  (((1 - α) ^ 2 + s) * (α * image + pF) - α * (1 - α) * ((1 - α) * image + pB)) / d

/-- The summary-form background update depending only on `α`, `I`, `s`, `p_F`, `p_B`, and `d`. -/
noncomputable def summaryBackground (data : LocalData ι) (α image : ℝ) : ℝ :=
  let s := data.totalWeight
  let pF := data.foregroundSum
  let pB := data.backgroundSum
  let d := data.summaryDenom α
  ((α ^ 2 + s) * ((1 - α) * image + pB) - α * (1 - α) * (α * image + pF)) / d

/-- The summary-form closed update vector. -/
noncomputable def summaryUpdate (data : LocalData ι) (α image : ℝ) : FBVec :=
  mkFBVec (data.summaryForeground α image) (data.summaryBackground α image)

theorem summaryDenom_eq_closedFormDenom (data : LocalData ι) (α : ℝ) :
    data.summaryDenom α = data.closedFormDenom α := rfl

@[simp] theorem summaryUpdate_foreground (data : LocalData ι) (α image : ℝ) :
    foreground (data.summaryUpdate α image) = data.summaryForeground α image := by
  simp [summaryUpdate]

@[simp] theorem summaryUpdate_background (data : LocalData ι) (α image : ℝ) :
    background (data.summaryUpdate α image) = data.summaryBackground α image := by
  simp [summaryUpdate]

theorem closedForm_foreground_eq_summary (data : LocalData ι) (α image : ℝ) :
    foreground (data.closedForm α image) = data.summaryForeground α image := by
  simp [LocalData.closedForm, summaryForeground, foreground, background, rhs, foregroundSum,
    backgroundSum, LocalData.summaryDenom]

theorem closedForm_background_eq_summary (data : LocalData ι) (α image : ℝ) :
    background (data.closedForm α image) = data.summaryBackground α image := by
  simp [LocalData.closedForm, summaryBackground, foreground, background, rhs, foregroundSum,
    backgroundSum, LocalData.summaryDenom]

theorem closedForm_eq_summaryUpdate (data : LocalData ι) (α image : ℝ) :
    data.closedForm α image = data.summaryUpdate α image := by
  apply ext_fbVec
  · exact data.closedForm_foreground_eq_summary α image
  · exact data.closedForm_background_eq_summary α image

theorem summaryDenom_pos_of_totalWeight_pos (data : LocalData ι) {α : ℝ}
    (h : 0 < data.totalWeight) :
    0 < data.summaryDenom α := by
  have hdet : 0 < data.closedFormDenom α := by
    rw [data.closedFormDenom_eq_det]
    exact data.systemMatrix_det_pos_of_totalWeight_pos (α := α) h
  simpa [summaryDenom_eq_closedFormDenom] using hdet

theorem summaryUpdate_solves_localSystem (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.localSystem α image (data.summaryUpdate α image) := by
  rw [← data.closedForm_eq_summaryUpdate α image]
  exact data.closedForm_solves_localSystem α image h

theorem summaryUpdate_stationary (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.stationary α image (data.summaryUpdate α image) := by
  rw [← data.closedForm_eq_summaryUpdate α image]
  exact data.closedForm_stationary α image h

section Examples

example (data : LocalData (Fin 1)) :
    data.foregroundSum = data.weights 0 * data.fgNeighbors 0 := by
  simp [foregroundSum]

example (data : LocalData (Fin 1)) :
    data.backgroundSum = data.weights 0 * data.bgNeighbors 0 := by
  simp [backgroundSum]

end Examples

end LocalData

end FastMLFE2
