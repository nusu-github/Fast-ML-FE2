import FastMLFE2.Theory.Level.Locality

namespace FastMLFE2.Theory.Canonical

/-!
Canonical authored builder data and construction for fixed-level Jacobi semantics.
-/

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level

structure CanonicalPixelData (κ ι : Type*) where
  alpha : κ → ℝ
  image : κ → ℝ
  neighborPixel : κ → ι → κ
  epsilonR : ℝ
  omega : ℝ

namespace CanonicalPixelData

variable {κ ι : Type*} [Fintype ι]

def toLocalContext
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ) : LocalContext ι :=
  { alphaCenter := data.alpha p
    imageValue := data.image p
    alphaNeighbor := fun j => data.alpha (data.neighborPixel p j)
    fgNeighbor := fun j => foreground (state (data.neighborPixel p j))
    bgNeighbor := fun j => background (state (data.neighborPixel p j))
    epsilonR := data.epsilonR
    omega := data.omega }

def canonicalBuilder
    (data : CanonicalPixelData κ ι) : LocalContextBuilder κ ι where
  build := data.toLocalContext

variable [DecidableEq κ]

def canonicalNeighborhood
    (data : CanonicalPixelData κ ι) : Neighborhood κ :=
  fun p => (Finset.univ : Finset ι).image (data.neighborPixel p)

theorem mem_canonicalNeighborhood
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (j : ι) :
    data.neighborPixel p j ∈ data.canonicalNeighborhood p := by
  refine Finset.mem_image.mpr ?_
  exact ⟨j, Finset.mem_univ j, rfl⟩

end CanonicalPixelData

end FastMLFE2.Theory.Canonical
