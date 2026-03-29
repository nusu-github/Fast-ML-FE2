import FastMLFE2.Canonical.Grid
import FastMLFE2.Canonical.MultilevelSchedule

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

structure RealLevelSpec where
  height : Nat
  width : Nat
  iterations : Nat
  heightPos : 0 < height
  widthPos : 0 < width
  deriving Repr

abbrev GridState (h w : Nat) := PixelState (Pixel h w)

abbrev SomeGridState :=
  Σ spec : RealLevelSpec, GridState spec.height spec.width

structure GridBuilderFamily where
  builder : (h w : Nat) → LocalContextBuilder (Pixel h w) (fun p => ValidDir p)

namespace RealLevelSpec

def numPixels (spec : RealLevelSpec) : Nat :=
  spec.height * spec.width

end RealLevelSpec

noncomputable def resizeSomeGridState
    (target : RealLevelSpec)
    (state : SomeGridState) : GridState target.height target.width := by
  rcases state with ⟨source, sourceState⟩
  letI : Fact (0 < source.height) := ⟨source.heightPos⟩
  letI : Fact (0 < source.width) := ⟨source.widthPos⟩
  exact nearestNeighborResize
    (hSrc := source.height) (wSrc := source.width)
    (hDst := target.height) (wDst := target.width) sourceState

noncomputable def multilevelStep
    (family : GridBuilderFamily)
    (target : RealLevelSpec)
    (state : SomeGridState) : SomeGridState :=
  let resized := resizeSomeGridState target state
  let builder := family.builder target.height target.width
  ⟨target, Nat.iterate (builder.jacobiStep) target.iterations resized⟩

noncomputable def multilevelRun
    (family : GridBuilderFamily)
    (seed : SomeGridState)
    (levels : List RealLevelSpec) : SomeGridState :=
  levels.foldl (fun state target => multilevelStep family target state) seed

@[simp] theorem multilevelRun_nil
    (family : GridBuilderFamily)
    (seed : SomeGridState) :
    multilevelRun family seed [] = seed := by
  rfl

end FastMLFE2.Canonical
