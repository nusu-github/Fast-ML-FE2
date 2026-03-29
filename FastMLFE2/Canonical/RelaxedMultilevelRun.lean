import FastMLFE2.Canonical.ClampedMultilevelRun
import FastMLFE2.Theorems.Grid.CanonicalStepStability
import FastMLFE2.Theorems.Iteration.RelaxedPairedJacobi

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

namespace GridPixelData

def stateBoxed
    {h w : Nat}
    (state : GridState h w) : Prop :=
  ∀ p, FastMLFE2.Theorems.Canonical.LocalUnknownBoxed (state p)

noncomputable def relaxedUpdateAt
    {h w : Nat}
    (data : GridPixelData h w)
    (r : ℝ)
    (innerIterations : Nat)
    (state : GridState h w)
    (p : Pixel h w) : LocalUnknown := by
  classical
  exact
    let ctx := data.localCtx p state
    if hboxed : stateBoxed state then
      if hfixed : clamp01 (LocalContext.closedFormSolution ctx) =
          LocalContext.closedFormSolution ctx then
        FastMLFE2.Theorems.LocalContext.endClampedRelaxedPairedJacobiIterate
          ctx r innerIterations (state p)
      else
        clamp01 (LocalContext.closedFormSolution ctx)
    else
      clamp01 (LocalContext.closedFormSolution ctx)

noncomputable def relaxedStep
    {h w : Nat}
    (data : GridPixelData h w)
    (r : ℝ)
    (innerIterations : Nat)
    (state : GridState h w) : GridState h w :=
  fun p => data.relaxedUpdateAt r innerIterations state p

end GridPixelData

noncomputable def relaxedCanonicalLevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (r : ℝ)
    (innerIterations : Nat)
    (state : GridState spec.height spec.width) : GridState spec.height spec.width :=
  Nat.iterate ((data spec.height spec.width).relaxedStep r innerIterations) spec.iterations state

noncomputable def relaxedCanonicalMultilevelStep
    (data : (h w : Nat) → GridPixelData h w)
    (r : ℝ)
    (innerIterations : Nat)
    (target : RealLevelSpec)
    (state : SomeGridState) : SomeGridState :=
  ⟨target, relaxedCanonicalLevelRun data target r innerIterations (resizeSomeGridState target state)⟩

noncomputable def relaxedCanonicalMultilevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (r : ℝ)
    (innerIterations : Nat)
    (seed : SomeGridState)
    (levels : List RealLevelSpec) : SomeGridState :=
  levels.foldl (fun state target => relaxedCanonicalMultilevelStep data r innerIterations target state)
    seed

@[simp] theorem relaxedCanonicalMultilevelRun_nil
    (data : (h w : Nat) → GridPixelData h w)
    (r : ℝ)
    (innerIterations : Nat)
    (seed : SomeGridState) :
    relaxedCanonicalMultilevelRun data r innerIterations seed [] = seed := by
  rfl

@[simp] theorem relaxedCanonicalMultilevelRun_cons
    (data : (h w : Nat) → GridPixelData h w)
    (r : ℝ)
    (innerIterations : Nat)
    (seed : SomeGridState)
    (target : RealLevelSpec)
    (levels : List RealLevelSpec) :
    relaxedCanonicalMultilevelRun data r innerIterations seed (target :: levels) =
      relaxedCanonicalMultilevelRun data r innerIterations
        (relaxedCanonicalMultilevelStep data r innerIterations target seed) levels := by
  rfl

end FastMLFE2.Canonical
