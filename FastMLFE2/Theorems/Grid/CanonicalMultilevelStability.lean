import FastMLFE2.Theorems.Grid.CanonicalMultilevelConvergence
import FastMLFE2.Theorems.Grid.MultilevelStability

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Level
open FastMLFE2.Canonical

namespace Canonical

noncomputable def canonicalLevelStabilityWitness
    (data : (h w : Nat) → GridPixelData h w)
    (target : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (runGap : RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun_nonneg : ∀ spec, 0 ≤ runGap spec)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (target spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (target spec) state + runGap spec)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (target dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (target src) state + transferGap src dst) :
    LevelStabilityWitness (fun spec => GridState spec.height spec.width) where
  resize := fun {src dst} state => resizeSomeGridState dst ⟨src, state⟩
  run := canonicalLevelRun data
  target := target
  error := fun spec state => gridStateError spec (target spec) state
  gain := gain
  transferGap := transferGap
  runGap := runGap
  error_nonneg := fun spec state => gridStateError_nonneg spec (target spec) state
  gain_nonneg := hgain_nonneg
  transferGap_nonneg := htransfer_nonneg
  runGap_nonneg := hrun_nonneg
  run_error_le := hrun
  transfer_error_le := htransfer

@[simp] theorem canonicalLevelStabilityWitness_multilevelStep_eq
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (runGap : RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun_nonneg : ∀ spec, 0 ≤ runGap spec)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state + runGap spec)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (spec : RealLevelSpec)
    (state : SomeGridState) :
    LevelStabilityWitness.multilevelStep
      (canonicalLevelStabilityWitness data targetState gain transferGap runGap
        hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
      spec state =
    multilevelStep (gridDataFamilyBuilder data) spec state := by
  rcases state with ⟨src, srcState⟩
  rfl

@[simp] theorem canonicalLevelStabilityWitness_multilevelRun_eq
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (runGap : RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun_nonneg : ∀ spec, 0 ≤ runGap spec)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state + runGap spec)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (seed : SomeGridState)
    (levels : List RealLevelSpec) :
    LevelStabilityWitness.multilevelRun
      (canonicalLevelStabilityWitness data targetState gain transferGap runGap
        hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
      seed levels =
    multilevelRun (gridDataFamilyBuilder data) seed levels := by
  induction levels generalizing seed with
  | nil =>
      rfl
  | cons spec rest ih =>
      simp [LevelStabilityWitness.multilevelRun_cons, multilevelRun_cons, ih]

theorem canonical_multilevel_stability_le
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (runGap : RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun_nonneg : ∀ spec, 0 ≤ runGap spec)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state + runGap spec)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (src : RealLevelSpec)
    (state : GridState src.height src.width)
    (levels : List RealLevelSpec) :
    gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).2 ≤
      LevelStabilityWitness.gainProduct
          (canonicalLevelStabilityWitness data targetState gain transferGap runGap
            hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
          levels *
        gridStateError src (targetState src) state +
      LevelStabilityWitness.transferSeries
          (canonicalLevelStabilityWitness data targetState gain transferGap runGap
            hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
          src levels +
      LevelStabilityWitness.runSeries
          (canonicalLevelStabilityWitness data targetState gain transferGap runGap
            hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
          levels := by
  simpa [canonicalLevelStabilityWitness_multilevelRun_eq]
    using LevelStabilityWitness.multilevelRun_error_le
      (canonicalLevelStabilityWitness data targetState gain transferGap runGap
        hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
      src state levels

theorem canonical_multilevel_singleton_stability_le
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (runGap : RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun_nonneg : ∀ spec, 0 ≤ runGap spec)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state + runGap spec)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (src target : RealLevelSpec)
    (state : GridState src.height src.width) :
    gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2 ≤
      gain target * gridStateError src (targetState src) state +
        gain target * transferGap src target + runGap target := by
  simpa [canonicalLevelStabilityWitness_multilevelRun_eq]
    using LevelStabilityWitness.multilevelRun_singleton_error_le
      (canonicalLevelStabilityWitness data targetState gain transferGap runGap
        hgain_nonneg htransfer_nonneg hrun_nonneg hrun htransfer)
      src target state

end Canonical

end FastMLFE2.Theorems
