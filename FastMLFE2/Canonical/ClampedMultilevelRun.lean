import FastMLFE2.Canonical.ClampPlacement
import FastMLFE2.Canonical.MultilevelRun

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

noncomputable def insideClampedLevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) : GridState spec.height spec.width :=
  CanonicalPixelData.insideClampedIterate
    ((data spec.height spec.width).toCanonicalPixelData)
    spec.iterations
    state

noncomputable def insideClampedMultilevelStep
    (data : (h w : Nat) → GridPixelData h w)
    (target : RealLevelSpec)
    (state : SomeGridState) : SomeGridState :=
  ⟨target, insideClampedLevelRun data target (resizeSomeGridState target state)⟩

noncomputable def insideClampedMultilevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (seed : SomeGridState)
    (levels : List RealLevelSpec) : SomeGridState :=
  levels.foldl (fun state target => insideClampedMultilevelStep data target state) seed

@[simp] theorem insideClampedMultilevelRun_nil
    (data : (h w : Nat) → GridPixelData h w)
    (seed : SomeGridState) :
    insideClampedMultilevelRun data seed [] = seed := by
  rfl

@[simp] theorem insideClampedMultilevelRun_cons
    (data : (h w : Nat) → GridPixelData h w)
    (seed : SomeGridState)
    (target : RealLevelSpec)
    (levels : List RealLevelSpec) :
    insideClampedMultilevelRun data seed (target :: levels) =
      insideClampedMultilevelRun data (insideClampedMultilevelStep data target seed) levels := by
  rfl

@[simp] theorem insideClampedMultilevelStep_sameSize_eq
    (data : (h w : Nat) → GridPixelData h w)
    (target : RealLevelSpec)
    (state : GridState target.height target.width) :
    insideClampedMultilevelStep data target ⟨target, state⟩ =
      ⟨target, insideClampedLevelRun data target state⟩ := by
  simp [insideClampedMultilevelStep]

@[simp] theorem insideClampedMultilevelRun_singleton
    (data : (h w : Nat) → GridPixelData h w)
    (seed : SomeGridState)
    (target : RealLevelSpec) :
    insideClampedMultilevelRun data seed [target] =
      insideClampedMultilevelStep data target seed := by
  simp [insideClampedMultilevelRun]

end FastMLFE2.Canonical
