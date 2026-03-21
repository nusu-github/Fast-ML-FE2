import FastMLFE2.MultilevelSpec

namespace FastMLFE2

abbrev Pixel (h w : Nat) := Fin h × Fin w

abbrev GrayImage (h w : Nat) := Pixel h w → ℝ

abbrev Offset := Int × Int

abbrev Neighborhood (h w k : Nat) := Pixel h w → Fin k → Offset

abbrev WeightRule (h w k : Nat) := GrayImage h w → Pixel h w → Fin k → Pixel h w → ℝ

def grayImageOps (h w : Nat) : ScalarImageOps (GrayImage h w) (Pixel h w) where
  sample image px := image px
  reconstruct f := f
  sample_reconstruct _ _ := rfl

theorem grayImage_ext {h w : Nat} {f g : GrayImage h w} (hfg : ∀ px, f px = g px) : f = g := by
  funext px
  exact hfg px

@[simp] theorem grayImageOps_sample (h w : Nat) (image : GrayImage h w) (px : Pixel h w) :
    (grayImageOps h w).sample image px = image px := rfl

@[simp] theorem grayImageOps_reconstruct (h w : Nat) (f : Pixel h w → ℝ) :
    (grayImageOps h w).reconstruct f = f := rfl

private theorem min_pred_lt_of_lt {n : Nat} (i : Fin n) (m : Nat) :
    min m (n - 1) < n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.pred_lt (Nat.ne_of_gt hn))

def clampCoord {n : Nat} (i : Fin n) (δ : Int) : Fin n :=
  let candidate : Nat := Int.toNat (i.1 + δ)
  ⟨min candidate (n - 1), min_pred_lt_of_lt i candidate⟩

def clampPixel {h w : Nat} (δ : Offset) (px : Pixel h w) : Pixel h w :=
  (clampCoord px.1 δ.1, clampCoord px.2 δ.2)

def neighborPixel {h w k : Nat} (neighbors : Neighborhood h w k)
    (px : Pixel h w) (t : Fin k) : Pixel h w :=
  clampPixel (neighbors px t) px

def localDataOfNeighborhood {h w k : Nat} (alpha fg bg : GrayImage h w)
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (px : Pixel h w) : LocalData (Fin k) where
  weights t := weightRule alpha px t (neighborPixel neighbors px t)
  fgNeighbors t := fg (neighborPixel neighbors px t)
  bgNeighbors t := bg (neighborPixel neighbors px t)

noncomputable def summaryRefinementModelOfNeighborhood {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k) :
    SummaryRefinementModel (GrayImage h w) (Pixel h w) (Fin k) where
  imageOps := grayImageOps h w
  localData _image alpha fg bg px := localDataOfNeighborhood alpha fg bg neighbors weightRule px

@[simp] theorem localDataOfNeighborhood_fgNeighbors {h w k : Nat} (alpha fg bg : GrayImage h w)
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (px : Pixel h w) (t : Fin k) :
    (localDataOfNeighborhood alpha fg bg neighbors weightRule px).fgNeighbors t =
      fg (neighborPixel neighbors px t) := rfl

@[simp] theorem localDataOfNeighborhood_bgNeighbors {h w k : Nat} (alpha fg bg : GrayImage h w)
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (px : Pixel h w) (t : Fin k) :
    (localDataOfNeighborhood alpha fg bg neighbors weightRule px).bgNeighbors t =
      bg (neighborPixel neighbors px t) := rfl

@[simp] theorem localDataOfNeighborhood_weights {h w k : Nat} (alpha fg bg : GrayImage h w)
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (px : Pixel h w) (t : Fin k) :
    (localDataOfNeighborhood alpha fg bg neighbors weightRule px).weights t =
      weightRule alpha px t (neighborPixel neighbors px t) := rfl

@[simp] theorem summaryRefinementModelOfNeighborhood_updateAt {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (image alpha fg bg : GrayImage h w) (px : Pixel h w) :
    (summaryRefinementModelOfNeighborhood neighbors weightRule).updateAt image alpha fg bg px =
      (localDataOfNeighborhood alpha fg bg neighbors weightRule px).summaryUpdate
        (alpha px) (image px) := by
  simp [SummaryRefinementModel.updateAt, summaryRefinementModelOfNeighborhood, grayImageOps]

@[simp] theorem summaryRefinementModelOfNeighborhood_refine_fst {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (image alpha fg bg : GrayImage h w) (px : Pixel h w) :
    ((
      summaryRefinementModelOfNeighborhood neighbors weightRule
    ).toRefinementOps.refine image alpha fg bg).1 px =
      foreground
        ((localDataOfNeighborhood alpha fg bg neighbors weightRule px).summaryUpdate
          (alpha px) (image px)) := by
  simp [SummaryRefinementModel.toRefinementOps, SummaryRefinementModel.refineForeground,
    SummaryRefinementModel.updateAt, summaryRefinementModelOfNeighborhood, grayImageOps,
    LocalData.summaryUpdate_foreground, localDataOfNeighborhood]

@[simp] theorem summaryRefinementModelOfNeighborhood_refine_snd {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (image alpha fg bg : GrayImage h w) (px : Pixel h w) :
    ((
      summaryRefinementModelOfNeighborhood neighbors weightRule
    ).toRefinementOps.refine image alpha fg bg).2 px =
      background
        ((localDataOfNeighborhood alpha fg bg neighbors weightRule px).summaryUpdate
          (alpha px) (image px)) := by
  simp [SummaryRefinementModel.toRefinementOps, SummaryRefinementModel.refineBackground,
    SummaryRefinementModel.updateAt, summaryRefinementModelOfNeighborhood, grayImageOps,
    LocalData.summaryUpdate_background, localDataOfNeighborhood]

section Examples

example : Pixel 1 1 := (0, 0)

example : clampPixel (1, -1) ((0 : Fin 1), (0 : Fin 1)) = ((0 : Fin 1), (0 : Fin 1)) := by
  rfl

example : Neighborhood 1 1 1 := fun _ _ => (0, 0)

example : GrayImage 1 1 := fun _ => 0

example (alpha fg bg : GrayImage 1 1) :
    (localDataOfNeighborhood alpha fg bg (fun _ _ => (0, 0)) (fun _ _ _ _ => 1)
      ((0 : Fin 1), (0 : Fin 1))).fgNeighbors (0 : Fin 1) =
      fg ((0 : Fin 1), (0 : Fin 1)) := by
  rfl

end Examples

end FastMLFE2
