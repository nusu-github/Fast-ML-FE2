import FastMLFE2.Theory.Theorems.ClosedForm

namespace FastMLFE2.Theory.Theorems

/-!
Channel-independent coefficient reuse for the local 2×2 system.

This layer fixes exactly what may be shared across channels: the matrix / determinant side
under shared alpha and regularization data. It intentionally does not claim `rhs` reuse.
-/

open FastMLFE2.Theory.Core

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/--
Weight-generating data shared across channels.

If two local contexts agree on these fields, then the coefficient matrix and its determinant
are channel-independent and may be reused. This relation deliberately does not mention the
signal-side fields `imageValue`, `fgNeighbor`, or `bgNeighbor`.
-/
structure SameWeightData (ctx₁ ctx₂ : LocalContext ι) : Prop where
  alphaCenter_eq : ctx₁.alphaCenter = ctx₂.alphaCenter
  alphaNeighbor_eq : ctx₁.alphaNeighbor = ctx₂.alphaNeighbor
  epsilonR_eq : ctx₁.epsilonR = ctx₂.epsilonR
  omega_eq : ctx₁.omega = ctx₂.omega

omit [Fintype ι] in
theorem neighborWeight_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameWeightData ctx₁ ctx₂)
    (j : ι) :
    ctx₁.neighborWeight j = ctx₂.neighborWeight j := by
  simp [FastMLFE2.Theory.Core.LocalContext.neighborWeight,
    h.alphaCenter_eq, h.alphaNeighbor_eq, h.epsilonR_eq, h.omega_eq]

theorem totalWeight_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.totalWeight = ctx₂.totalWeight := by
  unfold FastMLFE2.Theory.Core.LocalContext.totalWeight
  refine Finset.sum_congr rfl ?_
  intro j _
  exact neighborWeight_eq_of_sameWeightData h j

theorem normalMatrix_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix = ctx₂.normalMatrix := by
  have htw : ctx₁.totalWeight = ctx₂.totalWeight := totalWeight_eq_of_sameWeightData h
  ext i j
  fin_cases i <;> fin_cases j
  · rw [FastMLFE2.Theory.Core.LocalContext.normalMatrix,
      FastMLFE2.Theory.Core.LocalContext.normalMatrix]
    rw [htw]
    simp [h.alphaCenter_eq]
  · rw [FastMLFE2.Theory.Core.LocalContext.normalMatrix,
      FastMLFE2.Theory.Core.LocalContext.normalMatrix]
    simp [h.alphaCenter_eq]
  · rw [FastMLFE2.Theory.Core.LocalContext.normalMatrix,
      FastMLFE2.Theory.Core.LocalContext.normalMatrix]
    simp [h.alphaCenter_eq]
  · rw [FastMLFE2.Theory.Core.LocalContext.normalMatrix,
      FastMLFE2.Theory.Core.LocalContext.normalMatrix]
    rw [htw]
    simp [h.alphaCenter_eq]

theorem closedFormDenom_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameWeightData ctx₁ ctx₂) :
    closedFormDenom ctx₁ = closedFormDenom ctx₂ := by
  rw [closedFormDenom_eq_det, closedFormDenom_eq_det, normalMatrix_eq_of_sameWeightData h]

example (ctx₁ ctx₂ : LocalContext ι)
    (h :
      SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix = ctx₂.normalMatrix := by
  simpa using normalMatrix_eq_of_sameWeightData (ctx₁ := ctx₁) (ctx₂ := ctx₂) h

end LocalContext

end FastMLFE2.Theory.Theorems
