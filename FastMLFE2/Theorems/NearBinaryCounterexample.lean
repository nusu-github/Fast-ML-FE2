import FastMLFE2.Theorems.BinaryAlpha
import FastMLFE2.Theorems.ClampLocal

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

noncomputable def nearBinaryClampCounterexampleCtx : LocalContext PUnit where
  alphaCenter := (1 : ℝ) / 4
  imageValue := 0
  alphaNeighbor := fun _ => (1 : ℝ) / 4
  fgNeighbor := fun _ => 0
  bgNeighbor := fun _ => 1
  epsilonR := (1 : ℝ) / 8
  omega := (1 : ℝ) / 2

noncomputable def nearBinaryClampCounterexampleBinaryCtx : LocalContext PUnit :=
  nearBinaryClampCounterexampleCtx.withAlphaCenter 0

instance : CoreMathAssumptions nearBinaryClampCounterexampleCtx where
  epsilonPos := by norm_num [nearBinaryClampCounterexampleCtx]
  omegaNonneg := by norm_num [nearBinaryClampCounterexampleCtx]
  alphaCenterBounded := by
    constructor <;> norm_num [nearBinaryClampCounterexampleCtx]
  neighborNonempty := ⟨PUnit.unit⟩

instance : CoreMathAssumptions nearBinaryClampCounterexampleBinaryCtx where
  epsilonPos := by
    simp [nearBinaryClampCounterexampleBinaryCtx, nearBinaryClampCounterexampleCtx]
  omegaNonneg := by
    simp [nearBinaryClampCounterexampleBinaryCtx, nearBinaryClampCounterexampleCtx]
  alphaCenterBounded := by
    constructor <;>
      norm_num [nearBinaryClampCounterexampleBinaryCtx, nearBinaryClampCounterexampleCtx]
  neighborNonempty := ⟨PUnit.unit⟩

theorem closedFormSolution_nearBinaryClampCounterexample :
    closedFormSolution nearBinaryClampCounterexampleCtx =
      mkLocalUnknown (-((1 : ℝ) / 4)) ((1 : ℝ) / 4) := by
  ext i
  fin_cases i <;>
    norm_num [nearBinaryClampCounterexampleCtx, closedFormSolution, closedFormDenom,
      closedFormForegroundNumerator, closedFormBackgroundNumerator,
      FastMLFE2.Core.LocalContext.rhs,
      FastMLFE2.Core.LocalContext.foregroundSum,
      FastMLFE2.Core.LocalContext.backgroundSum,
      FastMLFE2.Core.LocalContext.totalWeight,
      FastMLFE2.Core.LocalContext.neighborWeight,
      foreground, background, mkLocalUnknown]

theorem clamp_closedFormSolution_nearBinaryClampCounterexample :
    clamp01 (closedFormSolution nearBinaryClampCounterexampleCtx) =
      mkLocalUnknown 0 ((1 : ℝ) / 4) := by
  rw [closedFormSolution_nearBinaryClampCounterexample]
  ext i
  fin_cases i <;> norm_num [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]

theorem closedFormSolution_nearBinaryClampCounterexampleBinary :
    closedFormSolution nearBinaryClampCounterexampleBinaryCtx =
      mkLocalUnknown 0 ((1 : ℝ) / 5) := by
  have hα : nearBinaryClampCounterexampleBinaryCtx.alphaCenter = 0 := by
    simp [nearBinaryClampCounterexampleBinaryCtx, nearBinaryClampCounterexampleCtx]
  rw [closedFormSolution_eq_of_alpha_zero
      (ctx := nearBinaryClampCounterexampleBinaryCtx) hα]
  ext i
  fin_cases i <;>
    norm_num [nearBinaryClampCounterexampleBinaryCtx, nearBinaryClampCounterexampleCtx,
      FastMLFE2.Core.LocalContext.foregroundSum,
      FastMLFE2.Core.LocalContext.backgroundSum,
      FastMLFE2.Core.LocalContext.totalWeight,
      FastMLFE2.Core.LocalContext.neighborWeight,
      foreground, background, mkLocalUnknown]

theorem localCost_nearBinaryClampCounterexample_binary :
    nearBinaryClampCounterexampleCtx.localCost
        (closedFormSolution nearBinaryClampCounterexampleBinaryCtx) =
      (41 : ℝ) / 400 := by
  rw [closedFormSolution_nearBinaryClampCounterexampleBinary]
  norm_num [nearBinaryClampCounterexampleCtx, FastMLFE2.Core.LocalContext.localCost,
    FastMLFE2.Core.LocalContext.compositingResidual_eq,
    FastMLFE2.Core.LocalContext.neighborWeight, foreground, background, mkLocalUnknown]

theorem localCost_nearBinaryClampCounterexample_clamped :
    nearBinaryClampCounterexampleCtx.localCost
        (clamp01 (closedFormSolution nearBinaryClampCounterexampleCtx)) =
      (27 : ℝ) / 256 := by
  rw [clamp_closedFormSolution_nearBinaryClampCounterexample]
  norm_num [nearBinaryClampCounterexampleCtx, FastMLFE2.Core.LocalContext.localCost,
    FastMLFE2.Core.LocalContext.compositingResidual_eq,
    FastMLFE2.Core.LocalContext.neighborWeight, foreground, background, mkLocalUnknown]

theorem localCost_nearBinaryClampCounterexample_binary_lt_clamped :
    nearBinaryClampCounterexampleCtx.localCost
        (closedFormSolution nearBinaryClampCounterexampleBinaryCtx) <
      nearBinaryClampCounterexampleCtx.localCost
        (clamp01 (closedFormSolution nearBinaryClampCounterexampleCtx)) := by
  rw [localCost_nearBinaryClampCounterexample_binary,
    localCost_nearBinaryClampCounterexample_clamped]
  norm_num

end LocalContext

end FastMLFE2.Theorems
