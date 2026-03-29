import FastMLFE2.Core.ClosedForm
import FastMLFE2.Theorems.Solvability.ClosedForm

namespace FastMLFE2.Theorems

/-!
Channel-independent coefficient reuse for the local 2×2 system.
-/

open FastMLFE2.Core
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- Weight-generating data shared across channels. -/
structure SameWeightData (ctx₁ ctx₂ : LocalContext ι) : Prop where
  alphaCenter_eq : ctx₁.alphaCenter = ctx₂.alphaCenter
  alphaNeighbor_eq : ctx₁.alphaNeighbor = ctx₂.alphaNeighbor
  epsilonR_eq : ctx₁.epsilonR = ctx₂.epsilonR
  omega_eq : ctx₁.omega = ctx₂.omega

/-- Exact RHS-sharing data. -/
structure SameRhsData (ctx₁ ctx₂ : LocalContext ι) : Prop extends SameWeightData ctx₁ ctx₂ where
  imageValue_eq : ctx₁.imageValue = ctx₂.imageValue
  fgNeighbor_eq : ctx₁.fgNeighbor = ctx₂.fgNeighbor
  bgNeighbor_eq : ctx₁.bgNeighbor = ctx₂.bgNeighbor

omit [Fintype ι] in
theorem neighborWeight_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) (j : ι) :
    ctx₁.neighborWeight j = ctx₂.neighborWeight j := by
  simp [LocalContext.neighborWeight,
    h.alphaCenter_eq, h.alphaNeighbor_eq, h.epsilonR_eq, h.omega_eq]

theorem totalWeight_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.totalWeight = ctx₂.totalWeight :=
  Finset.sum_congr rfl fun j _ => neighborWeight_eq_of_sameWeightData h j

theorem weightedMeanDenom_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.weightedMeanDenom = ctx₂.weightedMeanDenom := by
  rw [LocalContext.weightedMeanDenom, LocalContext.weightedMeanDenom,
    totalWeight_eq_of_sameWeightData h, h.alphaCenter_eq]

theorem normalMatrix_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix = ctx₂.normalMatrix := by
  have htw := totalWeight_eq_of_sameWeightData h
  ext i j; fin_cases i <;> fin_cases j <;> {
    rw [LocalContext.normalMatrix, LocalContext.normalMatrix]
    rw [htw]; simp [h.alphaCenter_eq]
  }

theorem closedFormDenom_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) :
    closedFormDenom ctx₁ = closedFormDenom ctx₂ := by
  rw [closedFormDenom_eq_det, closedFormDenom_eq_det, normalMatrix_eq_of_sameWeightData h]

theorem foregroundSum_eq_of_sameRhsData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.foregroundSum = ctx₂.foregroundSum :=
  Finset.sum_congr rfl fun j _ => by
    rw [neighborWeight_eq_of_sameWeightData h.toSameWeightData j,
      show ctx₁.fgNeighbor j = ctx₂.fgNeighbor j from congrFun h.fgNeighbor_eq j]

theorem backgroundSum_eq_of_sameRhsData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.backgroundSum = ctx₂.backgroundSum :=
  Finset.sum_congr rfl fun j _ => by
    rw [neighborWeight_eq_of_sameWeightData h.toSameWeightData j,
      show ctx₁.bgNeighbor j = ctx₂.bgNeighbor j from congrFun h.bgNeighbor_eq j]

theorem rhs_eq_of_sameRhsData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.rhs = ctx₂.rhs := by
  ext i; fin_cases i
  · calc ctx₁.rhs 0 = ctx₁.alphaCenter * ctx₁.imageValue + ctx₁.foregroundSum := by
          simp [LocalContext.rhs]
      _ = ctx₂.rhs 0 := by
        rw [h.toSameWeightData.alphaCenter_eq, h.imageValue_eq,
          foregroundSum_eq_of_sameRhsData h]; simp [LocalContext.rhs]
  · calc ctx₁.rhs 1 = (1 - ctx₁.alphaCenter) * ctx₁.imageValue + ctx₁.backgroundSum := by
          simp [LocalContext.rhs]
      _ = ctx₂.rhs 1 := by
        rw [h.toSameWeightData.alphaCenter_eq, h.imageValue_eq,
          backgroundSum_eq_of_sameRhsData h]; simp [LocalContext.rhs]

theorem not_forall_sameWeightData_rhs_eq :
    ¬ ∀ (ctx₁ ctx₂ : LocalContext Unit),
        SameWeightData ctx₁ ctx₂ → ctx₁.rhs = ctx₂.rhs := by
  intro hforall
  let ctx₁ : LocalContext Unit :=
    { alphaCenter := 1, imageValue := 0, alphaNeighbor := fun _ => 1,
      fgNeighbor := fun _ => 0, bgNeighbor := fun _ => 0,
      epsilonR := 1, omega := 0 }
  let ctx₂ : LocalContext Unit :=
    { alphaCenter := 1, imageValue := 1, alphaNeighbor := fun _ => 1,
      fgNeighbor := fun _ => 0, bgNeighbor := fun _ => 0,
      epsilonR := 1, omega := 0 }
  have := congrFun (hforall ctx₁ ctx₂ ⟨rfl, rfl, rfl, rfl⟩) 0
  simp [ctx₁, ctx₂, LocalContext.rhs, LocalContext.foregroundSum,
    LocalContext.neighborWeight] at this

example (ctx₁ ctx₂ : LocalContext ι) (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix = ctx₂.normalMatrix :=
  normalMatrix_eq_of_sameWeightData h

example (ctx₁ ctx₂ : LocalContext ι) (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.rhs = ctx₂.rhs :=
  rhs_eq_of_sameRhsData h

/-- The normal-matrix inverse is channel-independent: only weight data (α, ε_r, ω)
determines the inverse; image values and neighbor colors do not. -/
theorem normalMatrixInv_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix⁻¹ = ctx₂.normalMatrix⁻¹ := by
  congr 1
  exact normalMatrix_eq_of_sameWeightData h

end LocalContext

end FastMLFE2.Theorems
