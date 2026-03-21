import FastMLFE2.ConcreteImage

namespace FastMLFE2

structure PaperWeightParams where
  εr : ℝ
  ω : ℝ

def PaperWeightParams.Valid (params : PaperWeightParams) : Prop :=
  0 < params.εr ∧ 0 ≤ params.ω

def fourOffsets : Fin 4 → Offset :=
  ![(0, -1), (0, 1), (-1, 0), (1, 0)]

def fourNeighborhood {h w : Nat} : Neighborhood h w 4 :=
  fun _ t => fourOffsets t

def paperWeight {h w : Nat} (params : PaperWeightParams) : WeightRule h w 4 :=
  fun alpha px _t neighbor =>
    params.εr + params.ω * |alpha px - alpha neighbor|

def paperLocalData {h w : Nat} (params : PaperWeightParams)
    (alpha fg bg : GrayImage h w) (px : Pixel h w) : LocalData (Fin 4) :=
  localDataOfNeighborhood alpha fg bg fourNeighborhood (paperWeight params) px

noncomputable def paperSummaryRefinementModel {h w : Nat} (params : PaperWeightParams) :
    SummaryRefinementModel (GrayImage h w) (Pixel h w) (Fin 4) :=
  summaryRefinementModelOfNeighborhood fourNeighborhood (paperWeight params)

@[simp] theorem fourNeighborhood_apply {h w : Nat} (px : Pixel h w) (t : Fin 4) :
    fourNeighborhood px t = fourOffsets t := rfl

@[simp] theorem paperWeight_apply {h w : Nat} (params : PaperWeightParams)
    (alpha : GrayImage h w) (px : Pixel h w) (t : Fin 4) (neighbor : Pixel h w) :
    paperWeight params alpha px t neighbor =
      params.εr + params.ω * |alpha px - alpha neighbor| := rfl

theorem paperWeight_nonneg {h w : Nat} (params : PaperWeightParams)
    (hparams : params.Valid) (alpha : GrayImage h w) (px : Pixel h w)
    (t : Fin 4) (neighbor : Pixel h w) :
    0 ≤ paperWeight params alpha px t neighbor := by
  rcases hparams with ⟨hε, hω⟩
  have habs : 0 ≤ |alpha px - alpha neighbor| := abs_nonneg _
  simp [paperWeight]
  nlinarith [hε, hω, habs]

theorem paperWeight_pos {h w : Nat} (params : PaperWeightParams)
    (hparams : params.Valid) (alpha : GrayImage h w) (px : Pixel h w)
    (t : Fin 4) (neighbor : Pixel h w) :
    0 < paperWeight params alpha px t neighbor := by
  rcases hparams with ⟨hε, hω⟩
  have habs : 0 ≤ |alpha px - alpha neighbor| := abs_nonneg _
  simp [paperWeight]
  nlinarith [hε, hω, habs]

theorem paperLocalData_weight_pos {h w : Nat} (params : PaperWeightParams)
    (hparams : params.Valid) (alpha fg bg : GrayImage h w) (px : Pixel h w) (t : Fin 4) :
    0 < (paperLocalData params alpha fg bg px).weights t := by
  simpa [paperLocalData, localDataOfNeighborhood_weights] using
    paperWeight_pos params hparams alpha px t (neighborPixel fourNeighborhood px t)

theorem paperLocalData_weight_nonneg {h w : Nat} (params : PaperWeightParams)
    (hparams : params.Valid) (alpha fg bg : GrayImage h w) (px : Pixel h w) (t : Fin 4) :
    0 ≤ (paperLocalData params alpha fg bg px).weights t := by
  have hpos := paperLocalData_weight_pos params hparams alpha fg bg px t
  linarith

theorem paperLocalData_totalWeight_pos {h w : Nat} (params : PaperWeightParams)
    (hparams : params.Valid) (alpha fg bg : GrayImage h w) (px : Pixel h w) :
    0 < (paperLocalData params alpha fg bg px).totalWeight := by
  have hzero : 0 < (paperLocalData params alpha fg bg px).weights 0 := by
    exact paperLocalData_weight_pos params hparams alpha fg bg px 0
  have hle :
      (paperLocalData params alpha fg bg px).weights 0 ≤
        (paperLocalData params alpha fg bg px).totalWeight := by
    rw [LocalData.totalWeight]
    exact Finset.single_le_sum
      (fun t _ => paperLocalData_weight_nonneg params hparams alpha fg bg px t)
      (Finset.mem_univ 0)
  linarith

theorem paperUpdateAt_stationary {h w : Nat} (params : PaperWeightParams)
    (hparams : params.Valid) (image alpha fg bg : GrayImage h w) (px : Pixel h w) :
    (paperLocalData params alpha fg bg px).stationary (alpha px) (image px)
      ((paperSummaryRefinementModel params).updateAt image alpha fg bg px) := by
  have htotal : 0 < (paperLocalData params alpha fg bg px).totalWeight := by
    exact paperLocalData_totalWeight_pos params hparams alpha fg bg px
  simpa [paperSummaryRefinementModel, paperLocalData] using
    (paperSummaryRefinementModel params).updateAt_stationary_of_totalWeight_pos
      image alpha fg bg px htotal

section Examples

example :
    Neighborhood 3 4 4 :=
  fourNeighborhood

example (params : PaperWeightParams) (alpha : GrayImage 3 4)
    (px : Pixel 3 4) (t : Fin 4) :
    paperWeight params alpha px t (neighborPixel fourNeighborhood px t) =
      params.εr + params.ω * |alpha px - alpha (neighborPixel fourNeighborhood px t)| :=
  rfl

example (params : PaperWeightParams) (alpha fg bg image : GrayImage 3 4)
    (px : Pixel 3 4) :
    (paperSummaryRefinementModel params).updateAt image alpha fg bg px =
      (paperLocalData params alpha fg bg px).summaryUpdate (alpha px) (image px) := by
  simp [paperSummaryRefinementModel, paperLocalData]

example :
    fourNeighborhood ((0 : Fin 3), (0 : Fin 4)) 0 = (0, -1) := by
  rfl

example :
    neighborPixel fourNeighborhood ((0 : Fin 1), (0 : Fin 1)) 3 =
      ((0 : Fin 1), (0 : Fin 1)) := by
  rfl

end Examples

end FastMLFE2
