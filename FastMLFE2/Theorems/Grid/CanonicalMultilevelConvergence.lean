import FastMLFE2.Canonical.MultilevelPyramid
import FastMLFE2.Theorems.Grid.MultilevelConvergence
import FastMLFE2.Theorems.Iteration.JacobiContraction
import FastMLFE2.Theorems.Iteration.ContractionBounds

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Level
open FastMLFE2.Canonical

namespace Canonical

def basePixel (spec : RealLevelSpec) : Pixel spec.height spec.width :=
  (⟨0, spec.heightPos⟩, ⟨0, spec.widthPos⟩)

noncomputable def gridStateInfinityNorm
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) : ℝ :=
  letI : Nonempty (Pixel spec.height spec.width) := ⟨basePixel spec⟩
  (Finset.univ.image fun p : Pixel spec.height spec.width =>
      LocalContext.localInfinityNorm (state p)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

noncomputable def gridStateError
    (spec : RealLevelSpec)
    (target state : GridState spec.height spec.width) : ℝ :=
  gridStateInfinityNorm spec (fun p => state p - target p)

theorem gridStateInfinityNorm_nonneg
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) :
    0 ≤ gridStateInfinityNorm spec state := by
  unfold gridStateInfinityNorm
  letI : Nonempty (Pixel spec.height spec.width) := ⟨basePixel spec⟩
  have hmax :
      LocalContext.localInfinityNorm (state (basePixel spec)) ≤
        (Finset.univ.image fun p : Pixel spec.height spec.width =>
          LocalContext.localInfinityNorm (state p)).max'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) := by
    exact Finset.le_max'
      (s := Finset.univ.image fun p : Pixel spec.height spec.width =>
        LocalContext.localInfinityNorm (state p))
      (x := LocalContext.localInfinityNorm (state (basePixel spec)))
      (Finset.mem_image.mpr ⟨basePixel spec, Finset.mem_univ _, rfl⟩)
  exact le_trans (LocalContext.localInfinityNorm_nonneg (state (basePixel spec))) hmax

theorem localInfinityNorm_le_gridStateInfinityNorm
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width)
    (p : Pixel spec.height spec.width) :
    LocalContext.localInfinityNorm (state p) ≤ gridStateInfinityNorm spec state := by
  unfold gridStateInfinityNorm
  letI : Nonempty (Pixel spec.height spec.width) := ⟨basePixel spec⟩
  exact Finset.le_max'
    (s := Finset.univ.image fun q : Pixel spec.height spec.width =>
      LocalContext.localInfinityNorm (state q))
    (x := LocalContext.localInfinityNorm (state p))
    (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)

theorem gridStateError_nonneg
    (spec : RealLevelSpec)
    (target state : GridState spec.height spec.width) :
    0 ≤ gridStateError spec target state :=
  gridStateInfinityNorm_nonneg spec (fun p => state p - target p)

noncomputable def gridDataFamilyBuilder
    (data : (h w : Nat) → GridPixelData h w) : GridBuilderFamily where
  builder h w := (data h w).toCanonicalPixelData.canonicalBuilder

noncomputable def canonicalLevelRun
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) : GridState spec.height spec.width :=
  Nat.iterate ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep)
    spec.iterations state

noncomputable def canonicalLevelWitness
    (data : (h w : Nat) → GridPixelData h w)
    (target : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (target spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (target spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (target dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (target src) state + transferGap src dst) :
    LevelConvergenceWitness (fun spec => GridState spec.height spec.width) where
  resize := fun {src dst} state => resizeSomeGridState dst ⟨src, state⟩
  run := canonicalLevelRun data
  target := target
  error := fun spec state => gridStateError spec (target spec) state
  gain := gain
  transferGap := transferGap
  error_nonneg := fun spec state => gridStateError_nonneg spec (target spec) state
  gain_nonneg := hgain_nonneg
  gain_lt_one := hgain_lt_one
  transferGap_nonneg := htransfer_nonneg
  run_error_le := hrun
  transfer_error_le := htransfer

@[simp] theorem canonicalLevelWitness_multilevelStep_eq
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (spec : RealLevelSpec)
    (state : SomeGridState) :
    LevelConvergenceWitness.multilevelStep
      (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
        htransfer_nonneg hrun htransfer)
      spec state =
    multilevelStep (gridDataFamilyBuilder data) spec state := by
  rcases state with ⟨src, srcState⟩
  rfl

@[simp] theorem canonicalLevelWitness_multilevelRun_eq
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (seed : SomeGridState)
    (levels : List RealLevelSpec) :
    LevelConvergenceWitness.multilevelRun
      (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
        htransfer_nonneg hrun htransfer)
      seed levels =
    multilevelRun (gridDataFamilyBuilder data) seed levels := by
  induction levels generalizing seed with
  | nil =>
      rfl
  | cons spec rest ih =>
      simp [LevelConvergenceWitness.multilevelRun_cons, multilevelRun_cons, ih]

theorem canonical_multilevel_error_le
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (src : RealLevelSpec)
    (state : GridState src.height src.width)
    (levels : List RealLevelSpec) :
    gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ levels).2 ≤
      LevelConvergenceWitness.gainProduct
          (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
            htransfer_nonneg hrun htransfer)
          levels *
        gridStateError src (targetState src) state +
      LevelConvergenceWitness.transferSeries
          (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
            htransfer_nonneg hrun htransfer)
          src levels := by
  simpa [canonicalLevelWitness_multilevelRun_eq]
    using LevelConvergenceWitness.multilevelRun_error_le
      (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
        htransfer_nonneg hrun htransfer)
      src state levels

theorem canonical_multilevel_singleton_error_le
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (src target : RealLevelSpec)
    (state : GridState src.height src.width) :
    gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2 ≤
      gain target * gridStateError src (targetState src) state +
        gain target * transferGap src target := by
  simpa [canonicalLevelWitness_multilevelRun_eq]
    using LevelConvergenceWitness.multilevelRun_singleton_error_le
      (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
        htransfer_nonneg hrun htransfer)
      src target state

theorem canonical_multilevel_singleton_error_le_of_zero_transfer
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (src target : RealLevelSpec)
    (state : GridState src.height src.width)
    (hgap : transferGap src target = 0) :
    gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2 ≤
      gain target * gridStateError src (targetState src) state := by
  simpa [canonicalLevelWitness_multilevelRun_eq]
    using LevelConvergenceWitness.multilevelRun_singleton_error_le_of_zero_transfer
      (canonicalLevelWitness data targetState gain transferGap hgain_nonneg hgain_lt_one
        htransfer_nonneg hrun htransfer)
      src target state hgap

theorem canonical_singleton_terminationBound
    (data : (h w : Nat) → GridPixelData h w)
    (targetState : (spec : RealLevelSpec) → GridState spec.height spec.width)
    (gain : RealLevelSpec → ℝ)
    (transferGap : RealLevelSpec → RealLevelSpec → ℝ)
    (hgain_nonneg : ∀ spec, 0 ≤ gain spec)
    (hgain_lt_one : ∀ spec, gain spec < 1)
    (htransfer_nonneg : ∀ src dst, 0 ≤ transferGap src dst)
    (hrun : ∀ spec (state : GridState spec.height spec.width),
      gridStateError spec (targetState spec) (canonicalLevelRun data spec state) ≤
        gain spec * gridStateError spec (targetState spec) state)
    (htransfer : ∀ src dst (state : GridState src.height src.width),
      gridStateError dst (targetState dst) (resizeSomeGridState dst ⟨src, state⟩) ≤
        gridStateError src (targetState src) state + transferGap src dst)
    (src target : RealLevelSpec)
    (state : GridState src.height src.width)
    {scale eta rho : ℝ}
    (hx : gridStateError src (targetState src) state ≤ scale)
    (hgap : transferGap src target = 0)
    (hscale : 0 < scale)
    (heta : 0 < eta)
    (hrho0 : 0 < rho)
    (hrho1 : rho < 1)
    (hgain_pow : gain target = rho ^ target.iterations)
    (hk :
      1 + Real.log (scale / eta) / Real.log (1 / rho) ≤ (target.iterations + 1 : ℝ)) :
    gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2 ≤
      eta := by
  have hstep :=
    canonical_multilevel_singleton_error_le_of_zero_transfer
      data targetState gain transferGap hgain_nonneg hgain_lt_one htransfer_nonneg hrun htransfer
      src target state hgap
  have hchain : gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
        (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1)
        (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2 ≤
      scale * rho ^ target.iterations := by
    calc
      gridStateError (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1
          (targetState (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).1)
          (multilevelRun (gridDataFamilyBuilder data) ⟨src, state⟩ [target]).2 ≤
        gain target * gridStateError src (targetState src) state := hstep
      _ ≤ gain target * scale := by
        exact mul_le_mul_of_nonneg_left hx (hgain_nonneg target)
      _ = scale * rho ^ target.iterations := by
        rw [hgain_pow]
        ring
  exact error_le_of_log_threshold hchain hscale heta hrho0 hrho1 hk

end Canonical

end FastMLFE2.Theorems
