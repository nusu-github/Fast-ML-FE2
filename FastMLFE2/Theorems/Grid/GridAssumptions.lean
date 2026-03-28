import FastMLFE2.Assumptions.Grid
import FastMLFE2.Theorems.Grid.CanonicalBuilder

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Canonical
open FastMLFE2.Level

namespace GridPixelData

variable {h w : Nat}
variable (data : GridPixelData h w)
variable (state : PixelState (Pixel h w))
variable (p : Pixel h w)

instance coreMathAssumptions_of_gridMathAssumptions
    [GridMathAssumptions data]
    [Fact (Nonempty (ValidDir p))] :
    CoreMathAssumptions ((data.toCanonicalPixelData).canonicalBuilder.build p state) where
  epsilonPos := by simpa using GridMathAssumptions.epsilonPos (data := data)
  omegaNonneg := by simpa using GridMathAssumptions.omegaNonneg (data := data)
  alphaCenterBounded := by simpa using GridMathAssumptions.alphaBounded (data := data) p
  neighborNonempty := Fact.out

end GridPixelData

end FastMLFE2.Theorems
