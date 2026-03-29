import FastMLFE2.Theorems.Clamping.ClampPlacement
import FastMLFE2.Theorems.Clamping.ClampLocal
import FastMLFE2.Theorems.Iteration.BinaryAlpha

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Canonical
open FastMLFE2.Assumptions
open FastMLFE2.Level

def insideClampedFixedPointEta : PUnit → Type := fun _ => Fin 1

instance insideClampedFixedPointEtaInst
    (p : PUnit) : Fintype (insideClampedFixedPointEta p) := by
  change Fintype (Fin 1)
  infer_instance

instance insideClampedFixedPointEtaNonempty
    (p : PUnit) : Nonempty (insideClampedFixedPointEta p) := by
  cases p
  exact ⟨⟨0, by decide⟩⟩

instance insideClampedFixedPointEtaUnique
    (p : PUnit) : Unique (insideClampedFixedPointEta p) := by
  cases p
  exact { default := ⟨0, by decide⟩, uniq := fun x => Fin.ext (by omega) }

noncomputable def insideClampedFixedPointCounterexampleData :
    CanonicalPixelData PUnit insideClampedFixedPointEta where
  alpha := fun _ => 0
  image := fun _ => 0
  neighborPixel := fun _ _ => PUnit.unit
  epsilonR := 1
  omega := 0

def insideClampedConstState (f b : ℝ) : PixelState PUnit :=
  fun _ => mkLocalUnknown f b

@[simp] theorem insideClampedConstState_apply (f b : ℝ) :
    insideClampedConstState f b PUnit.unit = mkLocalUnknown f b := rfl

instance insideClampedFixedPointCounterexampleAssumptions
    (state : PixelState PUnit) :
    CoreMathAssumptions
      (insideClampedFixedPointCounterexampleData.toLocalContext PUnit.unit state) where
  epsilonPos := by
    norm_num [insideClampedFixedPointCounterexampleData, CanonicalPixelData.toLocalContext]
  omegaNonneg := by
    norm_num [insideClampedFixedPointCounterexampleData, CanonicalPixelData.toLocalContext]
  alphaCenterBounded := by
    constructor <;>
      norm_num [insideClampedFixedPointCounterexampleData, CanonicalPixelData.toLocalContext]
  neighborNonempty := insideClampedFixedPointEtaNonempty PUnit.unit

theorem insideClamped_binaryZero_rawStep_const (f b : ℝ) :
    insideClampedFixedPointCounterexampleData.rawStep (insideClampedConstState f b) PUnit.unit =
      mkLocalUnknown f (b / 2) := by
  rw [CanonicalPixelData.rawStep, Level.LocalContextBuilder.jacobiStep,
    Level.LocalContextBuilder.jacobiUpdateAt]
  let ctx :=
    insideClampedFixedPointCounterexampleData.toLocalContext PUnit.unit (insideClampedConstState f b)
  have hα : ctx.alphaCenter = 0 := by
    rfl
  have hsolve := FastMLFE2.Theorems.LocalContext.closedFormSolution_eq_of_alpha_zero ctx hα
  ext i
  fin_cases i
  · have hfg := congrArg foreground hsolve
    simpa [ctx, insideClampedFixedPointCounterexampleData, CanonicalPixelData.toLocalContext,
      insideClampedConstState, LocalContext.foregroundSum, LocalContext.totalWeight,
      LocalContext.neighborWeight, foreground, background, mkLocalUnknown] using hfg
  · have hbg := congrArg background hsolve
    calc
      background
          ((insideClampedFixedPointCounterexampleData.canonicalBuilder.build PUnit.unit
            (insideClampedConstState f b)).closedFormSolution)
        = b / (1 + 1) := by
            simpa [ctx, insideClampedFixedPointCounterexampleData, CanonicalPixelData.toLocalContext,
              insideClampedConstState, LocalContext.backgroundSum, LocalContext.totalWeight,
              LocalContext.neighborWeight, foreground, background, mkLocalUnknown] using hbg
      _ = b / 2 := by ring

theorem insideClamped_binaryZero_step_const (f b : ℝ) :
    insideClampedFixedPointCounterexampleData.insideClampedStep (insideClampedConstState f b) =
      insideClampedConstState (clamp01Scalar f) (clamp01Scalar (b / 2)) := by
  funext p
  cases p
  rw [CanonicalPixelData.insideClampedStep]
  rw [CanonicalPixelData.stateClamp01_apply]
  rw [insideClamped_binaryZero_rawStep_const]
  ext i <;> fin_cases i <;>
    simp [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]

theorem insideClamped_binaryZero_fixedPoint_of_fg_in_Icc
    {f : ℝ}
    (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) :
  insideClampedFixedPointCounterexampleData.insideClampedStep (insideClampedConstState f 0) =
      insideClampedConstState f 0 := by
  rw [insideClamped_binaryZero_step_const]
  funext p
  cases p
  ext i <;> fin_cases i
  · simpa [insideClampedConstState, foreground, mkLocalUnknown] using
      FastMLFE2.Theorems.LocalContext.clamp01Scalar_eq_self_of_mem_Icc hf0 hf1
  · simp [insideClampedConstState, background, mkLocalUnknown, clamp01Scalar]

theorem insideClamped_binaryZero_fixedPoint_zero :
    insideClampedFixedPointCounterexampleData.insideClampedStep (insideClampedConstState 0 0) =
      insideClampedConstState 0 0 := by
  exact insideClamped_binaryZero_fixedPoint_of_fg_in_Icc (by norm_num) (by norm_num)

theorem insideClamped_binaryZero_fixedPoint_one :
    insideClampedFixedPointCounterexampleData.insideClampedStep (insideClampedConstState 1 0) =
      insideClampedConstState 1 0 := by
  exact insideClamped_binaryZero_fixedPoint_of_fg_in_Icc (by norm_num) (by norm_num)

theorem insideClamped_binaryZero_fixedPoint_zero_ne_one :
    insideClampedConstState 0 0 ≠ insideClampedConstState 1 0 := by
  intro h
  have hfg := congrArg foreground (congrFun h PUnit.unit)
  simp [insideClampedConstState, foreground, mkLocalUnknown] at hfg

theorem insideClamped_binaryZero_iterate_fixed
    (k : Nat)
    {f : ℝ}
    (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) :
    insideClampedFixedPointCounterexampleData.insideClampedIterate k (insideClampedConstState f 0) =
      insideClampedConstState f 0 := by
  induction k with
  | zero =>
      simp [CanonicalPixelData.insideClampedIterate]
  | succ k ih =>
      rw [CanonicalPixelData.insideClampedIterate_succ, insideClamped_binaryZero_fixedPoint_of_fg_in_Icc hf0 hf1]
      exact ih

theorem insideClamped_two_invariant_trajectories (k : Nat) :
    insideClampedFixedPointCounterexampleData.insideClampedIterate k (insideClampedConstState 0 0) =
        insideClampedConstState 0 0 ∧
      insideClampedFixedPointCounterexampleData.insideClampedIterate k (insideClampedConstState 1 0) =
        insideClampedConstState 1 0 := by
  constructor
  · exact insideClamped_binaryZero_iterate_fixed k (by norm_num) (by norm_num)
  · exact insideClamped_binaryZero_iterate_fixed k (by norm_num) (by norm_num)

theorem insideClamped_not_unique_fixed_point :
    ¬ ∃ state : PixelState PUnit,
        insideClampedFixedPointCounterexampleData.insideClampedStep state = state ∧
          ∀ other : PixelState PUnit,
            insideClampedFixedPointCounterexampleData.insideClampedStep other = other →
              other = state := by
  intro h
  rcases h with ⟨state, hfixed, hunique⟩
  have hzero : insideClampedConstState 0 0 = state :=
    hunique _ insideClamped_binaryZero_fixedPoint_zero
  have hone : insideClampedConstState 1 0 = state :=
    hunique _ insideClamped_binaryZero_fixedPoint_one
  have : insideClampedConstState 0 0 = insideClampedConstState 1 0 := by
    rw [hzero, hone]
  exact insideClamped_binaryZero_fixedPoint_zero_ne_one this

end FastMLFE2.Theorems
