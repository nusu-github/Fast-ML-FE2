import FastMLFE2.ConcreteImage
import FastMLFE2.PrecomputedSummary

namespace FastMLFE2

/-- Parameters for the proof-oriented local specification model. This module defines the
simultaneous-update `spec` layer and is not the executable reference solver. -/
structure SpecWeightParams where
  εr : ℝ
  ω : ℝ

def SpecWeightParams.Valid (params : SpecWeightParams) : Prop :=
  0 < params.εr ∧ 0 ≤ params.ω

def fourOffsets : Fin 4 → Offset :=
  ![(0, -1), (0, 1), (-1, 0), (1, 0)]

def fourNeighborhood {h w : Nat} : Neighborhood h w 4 :=
  fun _ t => fourOffsets t

def specWeight {h w : Nat} (params : SpecWeightParams) : WeightRule h w 4 :=
  fun alpha px _t neighbor =>
    params.εr + params.ω * |alpha px - alpha neighbor|

def specLocalData {h w : Nat} (params : SpecWeightParams)
    (alpha fg bg : GrayImage h w) (px : Pixel h w) : LocalData (Fin 4) :=
  localDataOfNeighborhood alpha fg bg fourNeighborhood (specWeight params) px

/-- Proof-level specification of the four-neighbor local refinement step.
This is a simultaneous-update model and does not assert step-by-step equivalence with the
native executable reference solver. -/
noncomputable def specSummaryRefinementModel {h w : Nat} (params : SpecWeightParams) :
    SummaryRefinementModel (GrayImage h w) (Pixel h w) (Fin 4) :=
  summaryRefinementModelOfNeighborhood fourNeighborhood (specWeight params)

@[simp] theorem fourNeighborhood_apply {h w : Nat} (px : Pixel h w) (t : Fin 4) :
    fourNeighborhood px t = fourOffsets t := rfl

@[simp] theorem specWeight_apply {h w : Nat} (params : SpecWeightParams)
    (alpha : GrayImage h w) (px : Pixel h w) (t : Fin 4) (neighbor : Pixel h w) :
    specWeight params alpha px t neighbor =
      params.εr + params.ω * |alpha px - alpha neighbor| := rfl

theorem specWeight_nonneg {h w : Nat} (params : SpecWeightParams)
    (hparams : params.Valid) (alpha : GrayImage h w) (px : Pixel h w)
    (t : Fin 4) (neighbor : Pixel h w) :
    0 ≤ specWeight params alpha px t neighbor := by
  rcases hparams with ⟨hε, hω⟩
  have habs : 0 ≤ |alpha px - alpha neighbor| := abs_nonneg _
  simp [specWeight]
  nlinarith [hε, hω, habs]

theorem specWeight_pos {h w : Nat} (params : SpecWeightParams)
    (hparams : params.Valid) (alpha : GrayImage h w) (px : Pixel h w)
    (t : Fin 4) (neighbor : Pixel h w) :
    0 < specWeight params alpha px t neighbor := by
  rcases hparams with ⟨hε, hω⟩
  have habs : 0 ≤ |alpha px - alpha neighbor| := abs_nonneg _
  simp [specWeight]
  nlinarith [hε, hω, habs]

theorem specLocalData_weight_pos {h w : Nat} (params : SpecWeightParams)
    (hparams : params.Valid) (alpha fg bg : GrayImage h w) (px : Pixel h w) (t : Fin 4) :
    0 < (specLocalData params alpha fg bg px).weights t := by
  simpa [specLocalData, localDataOfNeighborhood_weights] using
    specWeight_pos params hparams alpha px t (neighborPixel fourNeighborhood px t)

theorem specLocalData_weight_nonneg {h w : Nat} (params : SpecWeightParams)
    (hparams : params.Valid) (alpha fg bg : GrayImage h w) (px : Pixel h w) (t : Fin 4) :
    0 ≤ (specLocalData params alpha fg bg px).weights t := by
  exact le_of_lt (specLocalData_weight_pos params hparams alpha fg bg px t)

theorem specLocalData_totalWeight_pos {h w : Nat} (params : SpecWeightParams)
    (hparams : params.Valid) (alpha fg bg : GrayImage h w) (px : Pixel h w) :
    0 < (specLocalData params alpha fg bg px).totalWeight := by
  have hzero : 0 < (specLocalData params alpha fg bg px).weights 0 := by
    exact specLocalData_weight_pos params hparams alpha fg bg px 0
  have hle :
      (specLocalData params alpha fg bg px).weights 0 ≤
        (specLocalData params alpha fg bg px).totalWeight := by
    rw [LocalData.totalWeight]
    exact Finset.single_le_sum
      (fun t _ => specLocalData_weight_nonneg params hparams alpha fg bg px t)
      (Finset.mem_univ 0)
  linarith

theorem specUpdateAt_stationary {h w : Nat} (params : SpecWeightParams)
    (hparams : params.Valid) (image alpha fg bg : GrayImage h w) (px : Pixel h w) :
    (specLocalData params alpha fg bg px).stationary (alpha px) (image px)
      ((specSummaryRefinementModel params).updateAt image alpha fg bg px) := by
  simpa [specSummaryRefinementModel, specLocalData] using
    (specSummaryRefinementModel params).updateAt_stationary_of_totalWeight_pos
      image alpha fg bg px (specLocalData_totalWeight_pos params hparams alpha fg bg px)

section Examples

example :
    Neighborhood 3 4 4 :=
  fourNeighborhood

example (params : SpecWeightParams) (alpha : GrayImage 3 4)
    (px : Pixel 3 4) (t : Fin 4) :
    specWeight params alpha px t (neighborPixel fourNeighborhood px t) =
      params.εr + params.ω * |alpha px - alpha (neighborPixel fourNeighborhood px t)| :=
  rfl

example (params : SpecWeightParams) (alpha fg bg image : GrayImage 3 4)
    (px : Pixel 3 4) :
    (specSummaryRefinementModel params).updateAt image alpha fg bg px =
      (specLocalData params alpha fg bg px).summaryUpdate (alpha px) (image px) := by
  simp [specSummaryRefinementModel, specLocalData]

example (params : SpecWeightParams) (alpha fg bg image : GrayImage 3 4)
    (hparams : params.Valid) (px : Pixel 3 4) :
    (specLocalData params alpha fg bg px).precomputedUpdate (alpha px) (image px) =
      (specLocalData params alpha fg bg px).summaryUpdate (alpha px) (image px) := by
  simpa using
    (specLocalData params alpha fg bg px).precomputedUpdate_eq_summaryUpdate
      (α := alpha px) (image := image px)
      (specLocalData_totalWeight_pos params hparams alpha fg bg px)

example :
    fourNeighborhood ((0 : Fin 3), (0 : Fin 4)) 0 = (0, -1) := by
  rfl

example :
    neighborPixel fourNeighborhood ((0 : Fin 1), (0 : Fin 1)) 3 =
      ((0 : Fin 1), (0 : Fin 1)) := by
  rfl

end Examples

end FastMLFE2
