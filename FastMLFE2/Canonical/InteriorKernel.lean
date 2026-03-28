import FastMLFE2.Canonical.GridContext

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

namespace GridPixelData

/-!
Interior-only specialized local context and solver surface.
-/

private theorem isValidDir_up_of_isInterior
    {h w : Nat}
    {p : Pixel h w}
    (hInterior : IsInterior p) :
    IsValidDir p Direction4.up := by
  exact hInterior.1

private theorem isValidDir_down_of_isInterior
    {h w : Nat}
    {p : Pixel h w}
    (hInterior : IsInterior p) :
    IsValidDir p Direction4.down := by
  exact hInterior.2.1

private theorem isValidDir_left_of_isInterior
    {h w : Nat}
    {p : Pixel h w}
    (hInterior : IsInterior p) :
    IsValidDir p Direction4.left := by
  exact hInterior.2.2.1

private theorem isValidDir_right_of_isInterior
    {h w : Nat}
    {p : Pixel h w}
    (hInterior : IsInterior p) :
    IsValidDir p Direction4.right := by
  exact hInterior.2.2.2

def interiorToValidDir
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p) :
    Direction4 → ValidDir p
  | .up => ⟨.up, isValidDir_up_of_isInterior hInterior⟩
  | .down => ⟨.down, isValidDir_down_of_isInterior hInterior⟩
  | .left => ⟨.left, isValidDir_left_of_isInterior hInterior⟩
  | .right => ⟨.right, isValidDir_right_of_isInterior hInterior⟩

@[simp] theorem interiorToValidDir_val
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p)
    (d : Direction4) :
    ((interiorToValidDir p hInterior d : ValidDir p) : Direction4) = d := by
  cases d <;> rfl

def interiorNeighborPixel
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p) :
    Direction4 → Pixel h w :=
  fun d => neighborPixel p (interiorToValidDir p hInterior d)

@[simp] theorem interiorNeighborPixel_eq_neighborPixel
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p)
    (d : Direction4) :
    interiorNeighborPixel p hInterior d = neighborPixel p (interiorToValidDir p hInterior d) := by
  rfl

def interiorLocalCtx
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    LocalContext Direction4 :=
  let ctx := data.localCtx p state
  { alphaCenter := ctx.alphaCenter
    imageValue := ctx.imageValue
    alphaNeighbor := fun d => ctx.alphaNeighbor (interiorToValidDir p hInterior d)
    fgNeighbor := fun d => ctx.fgNeighbor (interiorToValidDir p hInterior d)
    bgNeighbor := fun d => ctx.bgNeighbor (interiorToValidDir p hInterior d)
    epsilonR := ctx.epsilonR
    omega := ctx.omega }

noncomputable def interiorClosedFormSolution
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) : LocalUnknown :=
  FastMLFE2.Core.LocalContext.closedFormSolution
    (interiorLocalCtx data p state hInterior)

end GridPixelData

end FastMLFE2.Canonical
