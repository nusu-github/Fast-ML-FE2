import FastMLFE2.Level.Locality

namespace FastMLFE2.Canonical

/-!
Canonical authored builder data and construction for fixed-level Jacobi semantics.
-/

open FastMLFE2.Core
open FastMLFE2.Level

structure CanonicalPixelData (κ : Type*) (η : κ → Type*) [∀ p, Fintype (η p)] where
  alpha : κ → ℝ
  image : κ → ℝ
  neighborPixel : (p : κ) → η p → κ
  epsilonR : ℝ
  omega : ℝ

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

def toLocalContext
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state : PixelState κ) : LocalContext (η p) :=
  { alphaCenter := data.alpha p
    imageValue := data.image p
    alphaNeighbor := fun j => data.alpha (data.neighborPixel p j)
    fgNeighbor := fun j => foreground (state (data.neighborPixel p j))
    bgNeighbor := fun j => background (state (data.neighborPixel p j))
    epsilonR := data.epsilonR
    omega := data.omega }

def canonicalBuilder
    (data : CanonicalPixelData κ η) : LocalContextBuilder κ η where
  build := data.toLocalContext

variable [DecidableEq κ]

def canonicalNeighborhood
    (data : CanonicalPixelData κ η) : Neighborhood κ :=
  fun p => (Finset.univ : Finset (η p)).image (data.neighborPixel p)

theorem mem_canonicalNeighborhood
    (data : CanonicalPixelData κ η)
    (p : κ)
    (j : η p) :
    data.neighborPixel p j ∈ data.canonicalNeighborhood p := by
  refine Finset.mem_image.mpr ?_
  exact ⟨j, Finset.mem_univ j, rfl⟩

end CanonicalPixelData

end FastMLFE2.Canonical
