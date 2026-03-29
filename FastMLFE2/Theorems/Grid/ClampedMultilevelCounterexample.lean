import FastMLFE2.Canonical.ClampedMultilevelRun
import FastMLFE2.Theorems.Approximation.ClosedFormMeanResidual
import FastMLFE2.Theorems.Grid.GridNonempty
import FastMLFE2.Theorems.Grid.GridAssumptions
import FastMLFE2.Theorems.Iteration.BinaryAlpha
import FastMLFE2.Theorems.Solvability.NormalizedWeights

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Canonical
open FastMLFE2.Assumptions
open FastMLFE2.Level

noncomputable def insideClampedGridCounterexampleData : GridPixelData 1 2 where
  alpha := fun _ => 0
  image := fun _ => 0
  epsilonR := 1
  omega := 0

noncomputable def insideClampedGridCounterexampleFamily
    (h w : Nat) : GridPixelData h w where
  alpha := fun _ => 0
  image := fun _ => 0
  epsilonR := 1
  omega := 0

instance insideClampedGridCounterexampleAssumptions :
    GridMathAssumptions insideClampedGridCounterexampleData where
  epsilonPos := by norm_num [insideClampedGridCounterexampleData]
  omegaNonneg := by norm_num [insideClampedGridCounterexampleData]
  alphaBounded := by
    intro p
    constructor <;> norm_num [insideClampedGridCounterexampleData]

noncomputable def insideClampedGridCounterexampleSpec : RealLevelSpec where
  height := 1
  width := 2
  iterations := 1
  heightPos := by decide
  widthPos := by decide

def insideClampedGridConstState (f b : ℝ) : GridState 1 2 :=
  fun _ => mkLocalUnknown f b

@[simp] theorem insideClampedGridConstState_apply
    (f b : ℝ)
    (p : Pixel 1 2) :
    insideClampedGridConstState f b p = mkLocalUnknown f b := rfl

theorem insideClampedGrid_levelRun_fixed_of_fg_in_Icc
    {f : ℝ}
    (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) :
    insideClampedLevelRun
        insideClampedGridCounterexampleFamily
        insideClampedGridCounterexampleSpec
        (insideClampedGridConstState f 0) =
      insideClampedGridConstState f 0 := by
  simp [insideClampedLevelRun, insideClampedGridCounterexampleSpec]
  funext p
  change insideClampedGridCounterexampleData.toCanonicalPixelData.insideClampedStep
      (insideClampedGridConstState f 0) p = insideClampedGridConstState f 0 p
  let data := insideClampedGridCounterexampleData
  let ctx := data.toCanonicalPixelData.toLocalContext p (insideClampedGridConstState f 0)
  letI : Fact (2 ≤ 2) := ⟨by decide⟩
  haveI : Fact (Nonempty (ValidDir p)) := ⟨nonempty_validDir_of_width_two_le p⟩
  haveI : CoreMathAssumptions ctx := by
    simpa [ctx] using
      (FastMLFE2.Theorems.GridPixelData.coreMathAssumptions_of_gridMathAssumptions
        (data := data) (state := insideClampedGridConstState f 0) (p := p))
  have hα : ctx.alphaCenter = 0 := by
    rfl
  have hμF : ctx.foregroundMean = f := by
    have hfgNeighbor : ∀ j : ValidDir p, ctx.fgNeighbor j = f := by
      intro j
      change foreground
          (insideClampedGridConstState f 0
            (data.toCanonicalPixelData.neighborPixel p j)) = f
      simp [insideClampedGridConstState]
    calc
      ctx.foregroundMean =
          ∑ j,
            FastMLFE2.Theorems.LocalContext.normalizedWeight ctx j * ctx.fgNeighbor j := by
              simpa using
                FastMLFE2.Theorems.LocalContext.foregroundMean_eq_sum_normalizedWeight_mul ctx
      _ = ∑ j, FastMLFE2.Theorems.LocalContext.normalizedWeight ctx j * f := by
            simp [hfgNeighbor]
      _ = (∑ j, FastMLFE2.Theorems.LocalContext.normalizedWeight ctx j) * f := by
            rw [Finset.sum_mul]
      _ = f := by
            rw [FastMLFE2.Theorems.LocalContext.sum_normalizedWeight_eq_one]
            ring
  have hμB : ctx.backgroundMean = 0 := by
    have hbgNeighbor : ∀ j : ValidDir p, ctx.bgNeighbor j = 0 := by
      intro j
      change background
          (insideClampedGridConstState f 0
            (data.toCanonicalPixelData.neighborPixel p j)) = 0
      simp [insideClampedGridConstState]
    calc
      ctx.backgroundMean =
          ∑ j,
            FastMLFE2.Theorems.LocalContext.normalizedWeight ctx j * ctx.bgNeighbor j := by
              simpa using
                FastMLFE2.Theorems.LocalContext.backgroundMean_eq_sum_normalizedWeight_mul ctx
      _ = ∑ j, FastMLFE2.Theorems.LocalContext.normalizedWeight ctx j * 0 := by
            simp [hbgNeighbor]
      _ = 0 := by simp
  have himage : ctx.imageValue = 0 := by
    rfl
  have hfgClosed : foreground ((data.toCanonicalPixelData.canonicalBuilder.build p
      (insideClampedGridConstState f 0)).closedFormSolution) = ctx.foregroundMean := by
    have hfgEq := congrArg foreground
      (FastMLFE2.Theorems.LocalContext.meanResidualSolution_eq_closedFormSolution (ctx := ctx))
    have hfgMean :=
      FastMLFE2.Theorems.LocalContext.meanResidualSolution_foreground_of_alpha_zero ctx hα
    calc
      foreground ((data.toCanonicalPixelData.canonicalBuilder.build p
          (insideClampedGridConstState f 0)).closedFormSolution) =
          foreground (FastMLFE2.Theorems.LocalContext.meanResidualSolution ctx) := by
            simpa [ctx] using hfgEq.symm
      _ = ctx.foregroundMean := hfgMean
  have hbgClosed : background ((data.toCanonicalPixelData.canonicalBuilder.build p
      (insideClampedGridConstState f 0)).closedFormSolution) =
      ctx.backgroundMean + (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1) := by
    have hbgEq := congrArg background
      (FastMLFE2.Theorems.LocalContext.meanResidualSolution_eq_closedFormSolution (ctx := ctx))
    have hbgMean :=
      FastMLFE2.Theorems.LocalContext.meanResidualSolution_background_of_alpha_zero ctx hα
    calc
      background ((data.toCanonicalPixelData.canonicalBuilder.build p
          (insideClampedGridConstState f 0)).closedFormSolution) =
          background (FastMLFE2.Theorems.LocalContext.meanResidualSolution ctx) := by
            simpa [ctx] using hbgEq.symm
      _ = ctx.backgroundMean + (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1) :=
        hbgMean
  have hraw : data.toCanonicalPixelData.rawStep (insideClampedGridConstState f 0) p =
      mkLocalUnknown f 0 := by
    rw [CanonicalPixelData.rawStep, Level.LocalContextBuilder.jacobiStep,
      Level.LocalContextBuilder.jacobiUpdateAt]
    ext i
    fin_cases i
    · calc
        foreground
            ((data.toCanonicalPixelData.canonicalBuilder.build p
              (insideClampedGridConstState f 0)).closedFormSolution) =
            ctx.foregroundMean := hfgClosed
        _ = f := hμF
    · calc
        background
            ((data.toCanonicalPixelData.canonicalBuilder.build p
              (insideClampedGridConstState f 0)).closedFormSolution) =
            ctx.backgroundMean +
              (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1) := hbgClosed
        _ = 0 + (0 - 0) / (ctx.totalWeight + 1) := by rw [hμB, himage]
        _ = 0 := by
              have htw1 : ctx.totalWeight + 1 ≠ 0 := by
                linarith [FastMLFE2.Theorems.LocalContext.totalWeight_pos ctx]
              field_simp [htw1]
              ring
  rw [CanonicalPixelData.insideClampedStep, CanonicalPixelData.stateClamp01_apply, hraw]
  ext i
  fin_cases i
  · simp [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown, hf0, hf1]
  · simp [clamp01, clamp01Scalar, foreground, background, mkLocalUnknown]

theorem insideClampedGrid_multilevel_singleton_fixed_zero :
    insideClampedMultilevelRun
        insideClampedGridCounterexampleFamily
        ⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 0 0⟩
        [insideClampedGridCounterexampleSpec] =
      ⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 0 0⟩ := by
  rw [insideClampedMultilevelRun_singleton, insideClampedMultilevelStep_sameSize_eq]
  simpa using insideClampedGrid_levelRun_fixed_of_fg_in_Icc (f := 0) (by norm_num) (by norm_num)

theorem insideClampedGrid_multilevel_singleton_fixed_one :
    insideClampedMultilevelRun
        insideClampedGridCounterexampleFamily
        ⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 1 0⟩
        [insideClampedGridCounterexampleSpec] =
      ⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 1 0⟩ := by
  rw [insideClampedMultilevelRun_singleton, insideClampedMultilevelStep_sameSize_eq]
  simpa using insideClampedGrid_levelRun_fixed_of_fg_in_Icc (f := 1) (by norm_num) (by norm_num)

theorem insideClampedGrid_multilevel_singleton_zero_ne_one :
    (⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 0 0⟩ : SomeGridState) ≠
      ⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 1 0⟩ := by
  intro h
  have hsnd : insideClampedGridConstState 0 0 = insideClampedGridConstState 1 0 := by
    simpa [Sigma.mk.inj_iff] using (Sigma.mk.inj_iff.mp h).2
  have hfg := congrArg foreground
    (congrFun hsnd ((⟨0, by decide⟩, ⟨0, by decide⟩) : Pixel 1 2))
  simp [insideClampedGridConstState, foreground, mkLocalUnknown] at hfg

theorem insideClamped_multilevel_not_unique_fixed_point :
    ¬ ∃ state : SomeGridState,
        insideClampedMultilevelRun
            insideClampedGridCounterexampleFamily
            state [insideClampedGridCounterexampleSpec] = state ∧
          ∀ other : SomeGridState,
            insideClampedMultilevelRun
                insideClampedGridCounterexampleFamily
                other [insideClampedGridCounterexampleSpec] = other →
              other = state := by
  intro h
  rcases h with ⟨state, hfixed, hunique⟩
  have hzero :=
    hunique _ insideClampedGrid_multilevel_singleton_fixed_zero
  have hone :=
    hunique _ insideClampedGrid_multilevel_singleton_fixed_one
  have : (⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 0 0⟩ : SomeGridState) =
      ⟨insideClampedGridCounterexampleSpec, insideClampedGridConstState 1 0⟩ := by
    rw [hzero, hone]
  exact insideClampedGrid_multilevel_singleton_zero_ne_one this

end FastMLFE2.Theorems
