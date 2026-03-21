import FastMLFE2.SummaryForm

namespace FastMLFE2

/-- A minimal abstract notion of image resolution for the later multilevel development. -/
structure Resolution where
  width : Nat
  height : Nat
deriving DecidableEq, Repr

def Resolution.IsPositive (r : Resolution) : Prop :=
  0 < r.width ∧ 0 < r.height

/-- The resizing operations are intentionally abstract at this stage. -/
structure PyramidOps (Image : Type*) where
  resizeImage : Resolution → Image → Image
  resizeAlpha : Resolution → Image → Image
  initForeground : Image
  initBackground : Image

/-- One refinement step at a fixed resolution. -/
structure RefinementOps (Image : Type*) where
  refine : Image → Image → Image → Image → Image × Image

/-- Scalar-image interface for the current single-channel formalization. -/
structure ScalarImageOps (Image Pixel : Type*) where
  sample : Image → Pixel → ℝ
  reconstruct : (Pixel → ℝ) → Image
  sample_reconstruct : ∀ f i, sample (reconstruct f) i = f i

/--
Abstract data needed to lift the local summary-form solver to a whole-image refinement step.
The neighborhood extraction and weights are intentionally opaque here.
-/
structure SummaryRefinementModel (Image Pixel ι : Type*) [Fintype ι] [DecidableEq ι] where
  imageOps : ScalarImageOps Image Pixel
  localData : Image → Image → Image → Image → Pixel → LocalData ι

namespace SummaryRefinementModel

variable {Image Pixel ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def updateAt (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) (px : Pixel) : FBVec :=
  let data := model.localData image alpha fg bg px
  data.summaryUpdate (model.imageOps.sample alpha px) (model.imageOps.sample image px)

noncomputable def refineForeground (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) : Image :=
  model.imageOps.reconstruct (fun px => foreground (model.updateAt image alpha fg bg px))

noncomputable def refineBackground (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) : Image :=
  model.imageOps.reconstruct (fun px => background (model.updateAt image alpha fg bg px))

noncomputable def toRefinementOps (model : SummaryRefinementModel Image Pixel ι) :
    RefinementOps Image where
  refine image alpha fg bg :=
    (model.refineForeground image alpha fg bg, model.refineBackground image alpha fg bg)

@[simp] theorem sample_refineForeground (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) (px : Pixel) :
    model.imageOps.sample (model.refineForeground image alpha fg bg) px =
      foreground (model.updateAt image alpha fg bg px) := by
  simp [refineForeground, ScalarImageOps.sample_reconstruct]

@[simp] theorem sample_refineBackground (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) (px : Pixel) :
    model.imageOps.sample (model.refineBackground image alpha fg bg) px =
      background (model.updateAt image alpha fg bg px) := by
  simp [refineBackground, ScalarImageOps.sample_reconstruct]

@[simp] theorem sample_toRefinementOps_fst (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) (px : Pixel) :
    model.imageOps.sample ((model.toRefinementOps.refine image alpha fg bg).1) px =
      foreground (model.updateAt image alpha fg bg px) := by
  simp [toRefinementOps]

@[simp] theorem sample_toRefinementOps_snd (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) (px : Pixel) :
    model.imageOps.sample ((model.toRefinementOps.refine image alpha fg bg).2) px =
      background (model.updateAt image alpha fg bg px) := by
  simp [toRefinementOps]

theorem updateAt_stationary_of_totalWeight_pos (model : SummaryRefinementModel Image Pixel ι)
    (image alpha fg bg : Image) (px : Pixel)
    (h : 0 < (model.localData image alpha fg bg px).totalWeight) :
    (model.localData image alpha fg bg px).stationary
      (model.imageOps.sample alpha px) (model.imageOps.sample image px)
      (model.updateAt image alpha fg bg px) := by
  simpa [updateAt] using
    (model.localData image alpha fg bg px).summaryUpdate_stationary
      (model.imageOps.sample alpha px) (model.imageOps.sample image px) h

end SummaryRefinementModel

/-- Proof-first skeleton of Algorithm 1, leaving image semantics for later work. -/
structure MultilevelSpec (Image : Type*) where
  levels : List Resolution
  nSmallIterations : Nat := 10
  nBigIterations : Nat := 2
  pyramid : PyramidOps Image
  refinement : RefinementOps Image

def MultilevelSpec.WellFormed {Image : Type*} (spec : MultilevelSpec Image) : Prop :=
  spec.levels ≠ [] ∧ ∀ r ∈ spec.levels, r.IsPositive

noncomputable def SummaryRefinementModel.toMultilevelSpec
    {Image Pixel ι : Type*} [Fintype ι] [DecidableEq ι]
    (model : SummaryRefinementModel Image Pixel ι)
    (levels : List Resolution) (pyramid : PyramidOps Image)
    (nSmallIterations := 10) (nBigIterations := 2) :
    MultilevelSpec Image where
  levels := levels
  nSmallIterations := nSmallIterations
  nBigIterations := nBigIterations
  pyramid := pyramid
  refinement := model.toRefinementOps

noncomputable example {Image Pixel ι : Type*} [Fintype ι] [DecidableEq ι]
    (model : SummaryRefinementModel Image Pixel ι) :
    RefinementOps Image :=
  model.toRefinementOps

end FastMLFE2
