import FastMLFE2.Theory.Canonical.GridContext
import FastMLFE2.Theory.Theorems.ClosedForm
import FastMLFE2.Theory.Theorems.GridAssumptions
import FastMLFE2.Theory.Theorems.GridNonempty

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions
open FastMLFE2.Theory.Canonical
open FastMLFE2.Theory.Level

namespace GridPixelData

theorem localCtx_closedForm_solvesNormalEquation
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    [GridMathAssumptions data]
    (hN : Nonempty (ValidDir p)) :
    (data.localCtx p state).SolvesNormalEquation
      (LocalContext.closedFormSolution (data.localCtx p state)) := by
  letI : Fact (Nonempty (ValidDir p)) := ⟨hN⟩
  simpa [GridPixelData.localCtx] using
    (LocalContext.closedForm_solvesNormalEquation
      ((data.toCanonicalPixelData).canonicalBuilder.build p state))

theorem localCtx_closedForm_isCostStationary
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    [GridMathAssumptions data]
    (hN : Nonempty (ValidDir p)) :
    (data.localCtx p state).IsCostStationary
      (LocalContext.closedFormSolution (data.localCtx p state)) := by
  letI : Fact (Nonempty (ValidDir p)) := ⟨hN⟩
  simpa [GridPixelData.localCtx] using
    (LocalContext.closedForm_isCostStationary
      ((data.toCanonicalPixelData).canonicalBuilder.build p state))

private example
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    [GridMathAssumptions data]
    (hInterior : IsInterior p) :
    (data.localCtx p state).SolvesNormalEquation
      (LocalContext.closedFormSolution (data.localCtx p state)) := by
  exact localCtx_closedForm_solvesNormalEquation data p state
    (nonempty_validDir_of_isInterior p hInterior)

end GridPixelData

end FastMLFE2.Theory.Theorems
