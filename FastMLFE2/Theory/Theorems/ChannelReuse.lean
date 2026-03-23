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

/--
Exact RHS-sharing data.

`rhs` depends on the weight-generating data plus the signal-side fields `imageValue`,
`fgNeighbor`, and `bgNeighbor`.
-/
structure SameRhsData (ctx₁ ctx₂ : LocalContext ι) : Prop extends SameWeightData ctx₁ ctx₂ where
  imageValue_eq : ctx₁.imageValue = ctx₂.imageValue
  fgNeighbor_eq : ctx₁.fgNeighbor = ctx₂.fgNeighbor
  bgNeighbor_eq : ctx₁.bgNeighbor = ctx₂.bgNeighbor

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

theorem foregroundSum_eq_of_sameRhsData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.foregroundSum = ctx₂.foregroundSum := by
  unfold FastMLFE2.Theory.Core.LocalContext.foregroundSum
  refine Finset.sum_congr rfl ?_
  intro j _
  have hw := neighborWeight_eq_of_sameWeightData h.toSameWeightData j
  have hfg : ctx₁.fgNeighbor j = ctx₂.fgNeighbor j := by
    simpa using congrFun h.fgNeighbor_eq j
  rw [hw, hfg]

theorem backgroundSum_eq_of_sameRhsData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.backgroundSum = ctx₂.backgroundSum := by
  unfold FastMLFE2.Theory.Core.LocalContext.backgroundSum
  refine Finset.sum_congr rfl ?_
  intro j _
  have hw := neighborWeight_eq_of_sameWeightData h.toSameWeightData j
  have hbg : ctx₁.bgNeighbor j = ctx₂.bgNeighbor j := by
    simpa using congrFun h.bgNeighbor_eq j
  rw [hw, hbg]

theorem rhs_eq_of_sameRhsData
    {ctx₁ ctx₂ : LocalContext ι}
    (h : SameRhsData ctx₁ ctx₂) :
    ctx₁.rhs = ctx₂.rhs := by
  ext i
  fin_cases i
  · calc
      ctx₁.rhs 0 = ctx₁.alphaCenter * ctx₁.imageValue + ctx₁.foregroundSum := by
        simp [FastMLFE2.Theory.Core.LocalContext.rhs]
      _ = ctx₂.alphaCenter * ctx₂.imageValue + ctx₂.foregroundSum := by
        rw [h.toSameWeightData.alphaCenter_eq, h.imageValue_eq, foregroundSum_eq_of_sameRhsData h]
      _ = ctx₂.rhs 0 := by
        simp [FastMLFE2.Theory.Core.LocalContext.rhs]
  · calc
      ctx₁.rhs 1 = (1 - ctx₁.alphaCenter) * ctx₁.imageValue + ctx₁.backgroundSum := by
        simp [FastMLFE2.Theory.Core.LocalContext.rhs]
      _ = (1 - ctx₂.alphaCenter) * ctx₂.imageValue + ctx₂.backgroundSum := by
        rw [h.toSameWeightData.alphaCenter_eq, h.imageValue_eq, backgroundSum_eq_of_sameRhsData h]
      _ = ctx₂.rhs 1 := by
        simp [FastMLFE2.Theory.Core.LocalContext.rhs]

theorem not_forall_sameWeightData_rhs_eq :
    ¬ ∀ (ctx₁ ctx₂ : LocalContext Unit), SameWeightData ctx₁ ctx₂ → ctx₁.rhs = ctx₂.rhs := by
  intro hforall
  let ctx₁ : LocalContext Unit :=
    { alphaCenter := 1
      imageValue := 0
      alphaNeighbor := fun _ => 1
      fgNeighbor := fun _ => 0
      bgNeighbor := fun _ => 0
      epsilonR := 1
      omega := 0 }
  let ctx₂ : LocalContext Unit :=
    { alphaCenter := 1
      imageValue := 1
      alphaNeighbor := fun _ => 1
      fgNeighbor := fun _ => 0
      bgNeighbor := fun _ => 0
      epsilonR := 1
      omega := 0 }
  have hsame : SameWeightData ctx₁ ctx₂ := by
    refine ⟨rfl, rfl, rfl, rfl⟩
  have hrhs := hforall ctx₁ ctx₂ hsame
  have hfg :
      ctx₁.alphaCenter * ctx₁.imageValue + ctx₁.foregroundSum =
        ctx₂.alphaCenter * ctx₂.imageValue + ctx₂.foregroundSum := by
    simpa [FastMLFE2.Theory.Core.LocalContext.rhs] using congrFun hrhs 0
  simp [ctx₁, ctx₂, FastMLFE2.Theory.Core.LocalContext.foregroundSum,
    FastMLFE2.Theory.Core.LocalContext.neighborWeight] at hfg

example (ctx₁ ctx₂ : LocalContext ι)
    (h :
      SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix = ctx₂.normalMatrix := by
  simpa using normalMatrix_eq_of_sameWeightData (ctx₁ := ctx₁) (ctx₂ := ctx₂) h

example (ctx₁ ctx₂ : LocalContext ι)
    (h :
      SameRhsData ctx₁ ctx₂) :
    ctx₁.rhs = ctx₂.rhs := by
  simpa using rhs_eq_of_sameRhsData (ctx₁ := ctx₁) (ctx₂ := ctx₂) h

end LocalContext

end FastMLFE2.Theory.Theorems
