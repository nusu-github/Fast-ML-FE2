import FastMLFE2.Theorems.Clamping.ClampPlacement

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Canonical
open FastMLFE2.Assumptions
open FastMLFE2.Level

def clampPlacementConstState (f b : ℝ) : PixelState PUnit :=
  fun _ => mkLocalUnknown f b

@[simp] theorem clampPlacementConstState_apply (f b : ℝ) :
    clampPlacementConstState f b PUnit.unit = mkLocalUnknown f b := rfl

instance clampPlacementCounterexampleEtaNonempty
    (p : PUnit) : Nonempty (ClampPlacementCounterexampleEta p) := by
  cases p; exact ⟨⟨0, by decide⟩⟩

instance clampPlacementCounterexampleEtaUnique
    (p : PUnit) : Unique (ClampPlacementCounterexampleEta p) := by
  cases p
  exact { default := ⟨0, by decide⟩, uniq := fun x => Fin.ext (by omega) }

instance clampPlacementCounterexampleAssumptions
    (state : PixelState PUnit) :
    CoreMathAssumptions (clampPlacementCounterexampleData.toLocalContext PUnit.unit state) where
  epsilonPos := by norm_num [clampPlacementCounterexampleData, CanonicalPixelData.toLocalContext]
  omegaNonneg := by norm_num [clampPlacementCounterexampleData, CanonicalPixelData.toLocalContext]
  alphaCenterBounded := by
    constructor <;> norm_num [clampPlacementCounterexampleData, CanonicalPixelData.toLocalContext]
  neighborNonempty := clampPlacementCounterexampleEtaNonempty PUnit.unit

theorem clampPlacementCounterexample_gain :
    LocalContext.rawStepGain
        (clampPlacementCounterexampleData.toLocalContext PUnit.unit
          clampPlacementCounterexampleState0) = (7 : ℝ) / 6 := by
  norm_num [LocalContext.rawStepGain, clampPlacementCounterexampleData,
    clampPlacementCounterexampleState0, CanonicalPixelData.toLocalContext,
    LocalContext.totalWeight, LocalContext.neighborWeight, LocalContext.closedFormDenom]

theorem clampPlacementCounterexample_gain_gt_one :
    1 < LocalContext.rawStepGain
        (clampPlacementCounterexampleData.toLocalContext PUnit.unit
          clampPlacementCounterexampleState0) := by
  rw [clampPlacementCounterexample_gain]; norm_num

theorem clampPlacementCounterexample_rawStep_const (f b : ℝ) :
    clampPlacementCounterexampleData.rawStep
        (clampPlacementConstState f b) PUnit.unit =
      mkLocalUnknown
        (((11 : ℝ) / 12) * f - ((1 : ℝ) / 4) * b)
        ((-((1 : ℝ) / 4)) * f + ((1 : ℝ) / 4) * b) := by
  ext i; fin_cases i <;>
    simp [CanonicalPixelData.rawStep, CanonicalPixelData.canonicalBuilder,
      CanonicalPixelData.toLocalContext, Level.LocalContextBuilder.jacobiStep,
      Level.LocalContextBuilder.jacobiUpdateAt, clampPlacementCounterexampleData,
      clampPlacementConstState, LocalContext.closedFormSolution, LocalContext.closedFormDenom,
      LocalContext.rhs, LocalContext.foregroundSum, LocalContext.backgroundSum,
      LocalContext.totalWeight, LocalContext.neighborWeight, foreground, background, mkLocalUnknown]
    <;> ring_nf

theorem clampPlacementCounterexampleRaw1_value :
    clampPlacementCounterexampleRaw1 PUnit.unit =
      mkLocalUnknown (-((1 : ℝ) / 4)) ((1 : ℝ) / 4) := by
  simpa [clampPlacementCounterexampleRaw1, clampPlacementCounterexampleState0,
    CanonicalPixelData.rawIterate, clampPlacementConstState] using
    clampPlacementCounterexample_rawStep_const 0 1

theorem clampPlacementCounterexampleRaw1_eq_constState :
    clampPlacementCounterexampleRaw1 = clampPlacementConstState (-(1 / 4 : ℝ)) (1 / 4) := by
  funext p; cases p; exact clampPlacementCounterexampleRaw1_value

theorem clampPlacementCounterexampleInside1_value :
    clampPlacementCounterexampleInside1 PUnit.unit = mkLocalUnknown 0 ((1 : ℝ) / 4) := by
  have hraw :
      clampPlacementCounterexampleData.rawStep (clampPlacementConstState 0 1) PUnit.unit =
        mkLocalUnknown (-((1 : ℝ) / 4)) ((1 : ℝ) / 4) := by
    simpa using clampPlacementCounterexample_rawStep_const 0 1
  rw [show clampPlacementCounterexampleInside1 =
      CanonicalPixelData.insideClampedStep
        clampPlacementCounterexampleData clampPlacementCounterexampleState0 by rfl]
  rw [show clampPlacementCounterexampleState0 = clampPlacementConstState 0 1 by rfl]
  ext i; fin_cases i
  · rw [CanonicalPixelData.insideClampedStep, CanonicalPixelData.stateClamp01, hraw]
    norm_num [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]
  · rw [CanonicalPixelData.insideClampedStep, CanonicalPixelData.stateClamp01, hraw]
    norm_num [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]

theorem clampPlacementCounterexampleInside1_eq_constState :
    clampPlacementCounterexampleInside1 = clampPlacementConstState 0 (1 / 4) := by
  funext p; cases p; exact clampPlacementCounterexampleInside1_value

theorem clampPlacementCounterexampleRaw2_value :
    clampPlacementCounterexampleRaw2 PUnit.unit =
      mkLocalUnknown (-((7 : ℝ) / 24)) ((1 : ℝ) / 8) := by
  rw [show clampPlacementCounterexampleRaw2 =
    clampPlacementCounterexampleData.rawStep clampPlacementCounterexampleRaw1 from rfl,
    clampPlacementCounterexampleRaw1_eq_constState]
  have h := clampPlacementCounterexample_rawStep_const (-(1 / 4 : ℝ)) (1 / 4 : ℝ)
  norm_num at h; simpa [clampPlacementConstState] using h

theorem clampPlacementCounterexampleRaw2_eq_constState :
    clampPlacementCounterexampleRaw2 = clampPlacementConstState (-(7 / 24 : ℝ)) (1 / 8) := by
  funext p; cases p; exact clampPlacementCounterexampleRaw2_value

theorem clampPlacementCounterexampleInside2_value :
    clampPlacementCounterexampleInside2 PUnit.unit = mkLocalUnknown 0 ((1 : ℝ) / 16) := by
  have hraw :
      clampPlacementCounterexampleData.rawStep
          (clampPlacementConstState 0 ((1 : ℝ) / 4)) PUnit.unit =
        mkLocalUnknown (-((1 : ℝ) / 16)) ((1 : ℝ) / 16) := by
    have h := clampPlacementCounterexample_rawStep_const 0 ((1 : ℝ) / 4)
    norm_num at h
    simpa using h
  rw [show clampPlacementCounterexampleInside2 =
      clampPlacementCounterexampleData.insideClampedStep clampPlacementCounterexampleInside1 by rfl]
  rw [clampPlacementCounterexampleInside1_eq_constState]
  ext i; fin_cases i
  · rw [CanonicalPixelData.insideClampedStep, CanonicalPixelData.stateClamp01, hraw]
    norm_num [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]
  · rw [CanonicalPixelData.insideClampedStep, CanonicalPixelData.stateClamp01, hraw]
    norm_num [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]

theorem clampPlacementCounterexampleEnd2_value :
    clampPlacementCounterexampleEnd2 PUnit.unit = mkLocalUnknown 0 ((1 : ℝ) / 8) := by
  rw [show clampPlacementCounterexampleEnd2 =
      CanonicalPixelData.stateClamp01 clampPlacementCounterexampleRaw2 by rfl]
  rw [clampPlacementCounterexampleRaw2_eq_constState]
  ext i; fin_cases i <;>
    norm_num [CanonicalPixelData.stateClamp01, clamp01, clamp01Scalar,
      foreground, background, mkLocalUnknown]

theorem inside_iterate_two_ne_end_clamped_iterate_two :
    clampPlacementCounterexampleInside2 ≠ clampPlacementCounterexampleEnd2 := by
  intro h
  have := congrArg background (congrFun h PUnit.unit)
  rw [clampPlacementCounterexampleInside2_value, clampPlacementCounterexampleEnd2_value] at this
  simp [background, mkLocalUnknown] at this

theorem meanResidual_insideClamped_ne_endClamped :
    clampPlacementCounterexampleInside2 ≠ clampPlacementCounterexampleEnd2 :=
  inside_iterate_two_ne_end_clamped_iterate_two

end FastMLFE2.Theorems
