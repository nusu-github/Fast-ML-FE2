import FastMLFE2.Theory.Theorems.BlurFusionGap

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level
open FastMLFE2.Theory.Approximation

namespace LocalContextBuilder

abbrev SinglePixelNeighbors (_ : Unit) := Unit

/--
One-pixel self-neighbor builder used to witness that Blur-Fusion `x1` need not be a fixed point,
and that its update differs from the canonical Jacobi/closed-form step.
-/
noncomputable def blurFusionFixedPointCounterexampleBuilder :
    LocalContextBuilder Unit SinglePixelNeighbors where
  build _ state :=
    { alphaCenter := (1 : ℝ) / 2
      imageValue := 1
      alphaNeighbor := fun _ => (1 : ℝ) / 2
      fgNeighbor := fun _ => foreground (state ())
      bgNeighbor := fun _ => background (state ())
      epsilonR := 1
      omega := 0 }

noncomputable def blurFusionFixedPointCounterexampleState : PixelState Unit :=
  fun _ => mkLocalUnknown 0 0

noncomputable def blurFusionFixedPointCounterexampleX1 : PixelState Unit :=
  fun _ => mkLocalUnknown ((1 : ℝ) / 2) 0

theorem foreground_blurFusionUpdateAt_counterexample
    (state : PixelState Unit) :
    foreground
        (Approximation.LocalContextBuilder.blurFusionUpdateAt
          blurFusionFixedPointCounterexampleBuilder
          state ()) =
      foreground (state ()) +
        (1 / 2 : ℝ) *
          (1 - ((1 / 2 : ℝ) * foreground (state ()) + (1 / 2 : ℝ) * background (state ()))) := by
  have hfg : ((1 : ℝ) / 2) ≠ 0 := by norm_num
  have hbg : (1 - (1 : ℝ) / 2) ≠ 0 := by norm_num
  simp [Approximation.LocalContextBuilder.blurFusionUpdateAt,
    blurFusionFixedPointCounterexampleBuilder,
    Approximation.LocalContext.blurFusionOutput,
    Approximation.LocalContext.blurFusionForeground,
    Approximation.LocalContext.blurForegroundCorrection,
    Approximation.LocalContext.blurMeanResidual,
    Approximation.LocalContext.blurForegroundMean,
    Approximation.LocalContext.blurBackgroundMean,
    Approximation.LocalContext.blurForegroundSum,
    Approximation.LocalContext.blurBackgroundSum,
    Approximation.LocalContext.blurForegroundWeightSum,
    Approximation.LocalContext.blurBackgroundWeightSum,
    FastMLFE2.Theory.Core.LocalContext.compositingValue_eq,
    foreground, background, mkLocalUnknown]
  field_simp [hfg, hbg]
  ring

theorem background_blurFusionUpdateAt_counterexample
    (state : PixelState Unit) :
    background
        (Approximation.LocalContextBuilder.blurFusionUpdateAt
          blurFusionFixedPointCounterexampleBuilder
          state ()) =
      background (state ()) := by
  have hhalf : (1 - (1 / 2 : ℝ)) ≠ 0 := by norm_num
  simp [Approximation.LocalContextBuilder.blurFusionUpdateAt,
    blurFusionFixedPointCounterexampleBuilder,
    Approximation.LocalContext.blurFusionOutput,
    Approximation.LocalContext.blurBackgroundMean,
    Approximation.LocalContext.blurBackgroundSum,
    Approximation.LocalContext.blurBackgroundWeightSum,
    foreground, background, mkLocalUnknown]
  field_simp [hhalf]

theorem blurFusionUpdateAt_counterexample_eq_self_iff
    (state : PixelState Unit) :
    Approximation.LocalContextBuilder.blurFusionUpdateAt
        blurFusionFixedPointCounterexampleBuilder
        state () = state () ↔
      foreground (state ()) + background (state ()) = 2 := by
  constructor
  · intro h
    have hfg := congrArg foreground h
    rw [foreground_blurFusionUpdateAt_counterexample] at hfg
    nlinarith
  · intro hsum
    ext i
    fin_cases i
    · change foreground
          (Approximation.LocalContextBuilder.blurFusionUpdateAt
            blurFusionFixedPointCounterexampleBuilder state ()) =
        foreground (state ())
      rw [foreground_blurFusionUpdateAt_counterexample]
      nlinarith
    · change background
          (Approximation.LocalContextBuilder.blurFusionUpdateAt
            blurFusionFixedPointCounterexampleBuilder state ()) =
        background (state ())
      rw [background_blurFusionUpdateAt_counterexample]

theorem blurFusionUpdateAt_counterexample_initial :
    Approximation.LocalContextBuilder.blurFusionUpdateAt
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState () =
      mkLocalUnknown ((1 : ℝ) / 2) 0 := by
  ext i
  fin_cases i <;>
    norm_num [blurFusionFixedPointCounterexampleBuilder,
      blurFusionFixedPointCounterexampleState,
      Approximation.LocalContextBuilder.blurFusionUpdateAt,
      Approximation.LocalContext.blurFusionOutput,
      Approximation.LocalContext.blurFusionForeground,
      Approximation.LocalContext.blurForegroundCorrection,
      Approximation.LocalContext.blurMeanResidual,
      Approximation.LocalContext.blurForegroundMean,
      Approximation.LocalContext.blurBackgroundMean,
      Approximation.LocalContext.blurForegroundSum,
      Approximation.LocalContext.blurBackgroundSum,
      Approximation.LocalContext.blurForegroundWeightSum,
      Approximation.LocalContext.blurBackgroundWeightSum,
      FastMLFE2.Theory.Core.LocalContext.compositingValue_eq,
      FastMLFE2.Theory.Core.LocalContext.compositingValue,
      foreground, background, mkLocalUnknown]

theorem blurFusionX1_counterexample :
    Approximation.LocalContextBuilder.blurFusionX1
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState =
      blurFusionFixedPointCounterexampleX1 := by
  funext p
  cases p
  rw [Approximation.LocalContextBuilder.blurFusionX1_eq_blurFusionStep]
  simpa [Approximation.LocalContextBuilder.blurFusionStep_apply,
    blurFusionFixedPointCounterexampleX1] using
    blurFusionUpdateAt_counterexample_initial

theorem jacobiUpdateAt_counterexample_initial :
    LocalContextBuilder.jacobiUpdateAt
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState () =
      mkLocalUnknown ((1 : ℝ) / 3) ((1 : ℝ) / 3) := by
  ext i
  fin_cases i <;>
    norm_num [blurFusionFixedPointCounterexampleBuilder,
      blurFusionFixedPointCounterexampleState,
      LocalContextBuilder.jacobiUpdateAt,
      FastMLFE2.Theory.Theorems.LocalContext.closedFormSolution,
      FastMLFE2.Theory.Theorems.LocalContext.closedFormDenom,
      FastMLFE2.Theory.Theorems.LocalContext.closedFormForegroundNumerator,
      FastMLFE2.Theory.Theorems.LocalContext.closedFormBackgroundNumerator,
      FastMLFE2.Theory.Core.LocalContext.rhs,
      FastMLFE2.Theory.Core.LocalContext.foregroundSum,
      FastMLFE2.Theory.Core.LocalContext.backgroundSum,
      FastMLFE2.Theory.Core.LocalContext.totalWeight,
      FastMLFE2.Theory.Core.LocalContext.neighborWeight,
      foreground, background, mkLocalUnknown]

theorem blurFusionUpdateAt_counterexample_x1 :
    Approximation.LocalContextBuilder.blurFusionUpdateAt
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleX1 () =
      mkLocalUnknown ((7 : ℝ) / 8) 0 := by
  ext i
  fin_cases i <;>
    norm_num [blurFusionFixedPointCounterexampleBuilder,
      blurFusionFixedPointCounterexampleX1,
      Approximation.LocalContextBuilder.blurFusionUpdateAt,
      Approximation.LocalContext.blurFusionOutput,
      Approximation.LocalContext.blurFusionForeground,
      Approximation.LocalContext.blurForegroundCorrection,
      Approximation.LocalContext.blurMeanResidual,
      Approximation.LocalContext.blurForegroundMean,
      Approximation.LocalContext.blurBackgroundMean,
      Approximation.LocalContext.blurForegroundSum,
      Approximation.LocalContext.blurBackgroundSum,
      Approximation.LocalContext.blurForegroundWeightSum,
      Approximation.LocalContext.blurBackgroundWeightSum,
      FastMLFE2.Theory.Core.LocalContext.compositingValue_eq,
      FastMLFE2.Theory.Core.LocalContext.compositingValue,
      FastMLFE2.Theory.Core.uVec,
      foreground, background, mkLocalUnknown]

theorem blurFusionX2_counterexample :
    Approximation.LocalContextBuilder.blurFusionX2
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState () =
      mkLocalUnknown ((7 : ℝ) / 8) 0 := by
  rw [Approximation.LocalContextBuilder.blurFusionX2_eq_blurFusionStep_comp]
  rw [← Approximation.LocalContextBuilder.blurFusionX1_eq_blurFusionStep
      (builder := blurFusionFixedPointCounterexampleBuilder)]
  rw [blurFusionX1_counterexample]
  simpa [Approximation.LocalContextBuilder.blurFusionStep_apply] using
    blurFusionUpdateAt_counterexample_x1

theorem blurFusionX1_ne_jacobiStep_counterexample :
    Approximation.LocalContextBuilder.blurFusionUpdateAt
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState () ≠
      LocalContextBuilder.jacobiUpdateAt
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState () := by
  rw [blurFusionUpdateAt_counterexample_initial, jacobiUpdateAt_counterexample_initial]
  intro h
  have hfg := congrArg foreground h
  norm_num at hfg

theorem blurFusionX1_not_fixed_counterexample :
    Approximation.LocalContextBuilder.blurFusionStep
        blurFusionFixedPointCounterexampleBuilder
        (Approximation.LocalContextBuilder.blurFusionX1
          blurFusionFixedPointCounterexampleBuilder
          blurFusionFixedPointCounterexampleState) () ≠
      Approximation.LocalContextBuilder.blurFusionX1
        blurFusionFixedPointCounterexampleBuilder
        blurFusionFixedPointCounterexampleState () := by
  rw [blurFusionX1_counterexample]
  rw [Approximation.LocalContextBuilder.blurFusionStep_apply]
  rw [blurFusionUpdateAt_counterexample_x1, blurFusionFixedPointCounterexampleX1]
  intro h
  have hfg := congrArg foreground h
  norm_num at hfg

theorem blurFusionCounterexample_initial_not_fixed :
    ¬ (foreground (blurFusionFixedPointCounterexampleState ()) +
        background (blurFusionFixedPointCounterexampleState ()) = 2) := by
  norm_num [blurFusionFixedPointCounterexampleState, foreground, background, mkLocalUnknown]

end LocalContextBuilder

end FastMLFE2.Theory.Theorems
