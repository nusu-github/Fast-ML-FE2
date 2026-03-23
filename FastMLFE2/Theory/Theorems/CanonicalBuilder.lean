import FastMLFE2.Theory.Canonical.Builder

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level
open FastMLFE2.Theory.Canonical

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

@[simp] theorem canonicalBuilder_alphaCenter
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).alphaCenter = data.alpha p := by
  rfl

@[simp] theorem canonicalBuilder_imageValue
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).imageValue = data.image p := by
  rfl

@[simp] theorem canonicalBuilder_alphaNeighbor
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ)
    (j : η p) :
    (data.canonicalBuilder.build p state).alphaNeighbor j =
      data.alpha (data.neighborPixel p j) := by
  rfl

@[simp] theorem canonicalBuilder_fgNeighbor
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ)
    (j : η p) :
    (data.canonicalBuilder.build p state).fgNeighbor j =
      foreground (state (data.neighborPixel p j)) := by
  rfl

@[simp] theorem canonicalBuilder_bgNeighbor
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ)
    (j : η p) :
    (data.canonicalBuilder.build p state).bgNeighbor j =
      background (state (data.neighborPixel p j)) := by
  rfl

@[simp] theorem canonicalBuilder_epsilonR
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).epsilonR = data.epsilonR := by
  rfl

@[simp] theorem canonicalBuilder_omega
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).omega = data.omega := by
  rfl

variable [DecidableEq κ]

theorem canonicalBuilder_local
    (data : CanonicalPixelData κ η) :
    BuilderLocal data.canonicalBuilder data.canonicalNeighborhood := by
  intro p state₁ state₂ hEq
  cases data with
  | mk alpha image neighborPixel epsilonR omega =>
      have hfg :
          (fun j => foreground (state₁ (neighborPixel p j))) =
            (fun j => foreground (state₂ (neighborPixel p j))) := by
        funext j
        have hmem : neighborPixel p j ∈ (Finset.univ : Finset (η p)).image (neighborPixel p) := by
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
        exact congrArg foreground (hEq _ hmem)
      have hbg :
          (fun j => background (state₁ (neighborPixel p j))) =
            (fun j => background (state₂ (neighborPixel p j))) := by
        funext j
        have hmem : neighborPixel p j ∈ (Finset.univ : Finset (η p)).image (neighborPixel p) := by
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
        exact congrArg background (hEq _ hmem)
      simp [CanonicalPixelData.canonicalBuilder, CanonicalPixelData.toLocalContext, hfg, hbg]

end CanonicalPixelData

end FastMLFE2.Theory.Theorems
