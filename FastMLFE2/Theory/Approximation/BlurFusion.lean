import FastMLFE2.Theory.Level.Jacobi

namespace FastMLFE2.Theory.Approximation

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level

/-!
Idealized Blur-Fusion approximation semantics.

This module captures the real-valued PhotoRoom-style approximation described in `main2.tex`,
without the authored implementation regularizer `+1e-5`. The goal is to expose a precise
surrogate objective and its induced update map for later gap/fixed-point analysis.
-/

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- Blur-Fusion foreground weight mass `∑ α_j`. -/
def blurForegroundWeightSum (ctx : LocalContext ι) : ℝ :=
  ∑ j, ctx.alphaNeighbor j

/-- Blur-Fusion background weight mass `∑ (1 - α_j)`. -/
def blurBackgroundWeightSum (ctx : LocalContext ι) : ℝ :=
  ∑ j, (1 - ctx.alphaNeighbor j)

/-- Blur-Fusion foreground weighted sum `∑ α_j F_j`. -/
def blurForegroundSum (ctx : LocalContext ι) : ℝ :=
  ∑ j, ctx.alphaNeighbor j * ctx.fgNeighbor j

/-- Blur-Fusion background weighted sum `∑ (1 - α_j) B_j`. -/
def blurBackgroundSum (ctx : LocalContext ι) : ℝ :=
  ∑ j, (1 - ctx.alphaNeighbor j) * ctx.bgNeighbor j

/-- The stage-one Blur-Fusion foreground estimate `\hat F_i`. -/
noncomputable def blurForegroundMean (ctx : LocalContext ι) : ℝ :=
  blurForegroundSum ctx / blurForegroundWeightSum ctx

/-- The stage-one Blur-Fusion background estimate `\hat B_i`. -/
noncomputable def blurBackgroundMean (ctx : LocalContext ι) : ℝ :=
  blurBackgroundSum ctx / blurBackgroundWeightSum ctx

/--
The separated smoothness surrogate from PhotoRoom Eq. (3), where the foreground and background
channels use `α_j` and `1 - α_j` directly instead of Germer's shared
`ε_r + ω |α_i - α_j|` weight.
-/
def blurSmoothCost (ctx : LocalContext ι) (g : LocalUnknown) : ℝ :=
  ∑ j, (ctx.alphaNeighbor j * (foreground g - ctx.fgNeighbor j) ^ 2 +
    (1 - ctx.alphaNeighbor j) * (background g - ctx.bgNeighbor j) ^ 2)

/--
The joint Blur-Fusion surrogate objective corresponding to PhotoRoom Eq. (3).

This is not the canonical Germer local cost; it replaces the shared neighbor weight with
channel-separated alpha masks.
-/
def blurLocalCost (ctx : LocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.compositingResidual g ^ 2 + blurSmoothCost ctx g

/--
The stage-two surrogate from PhotoRoom Eq. (6), centered at the stage-one weighted means.
-/
noncomputable def blurStageTwoCost (ctx : LocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.compositingResidual g ^ 2 +
    (foreground g - blurForegroundMean ctx) ^ 2 +
    (background g - blurBackgroundMean ctx) ^ 2

/--
The one-dimensional stage-two objective obtained by freezing the background at `\hat B_i` and
optimizing only the foreground component.
-/
noncomputable def blurForegroundStageTwoCost (ctx : LocalContext ι) (foregroundValue : ℝ) : ℝ :=
  (ctx.alphaCenter * foregroundValue + (1 - ctx.alphaCenter) * blurBackgroundMean ctx -
      ctx.imageValue) ^ 2 +
    (foregroundValue - blurForegroundMean ctx) ^ 2

/-- The compositing residual evaluated at the stage-one Blur-Fusion mean pair. -/
noncomputable def blurMeanResidual (ctx : LocalContext ι) : ℝ :=
  ctx.imageValue -
    ctx.compositingValue (mkLocalUnknown (blurForegroundMean ctx) (blurBackgroundMean ctx))

/-- The explicit foreground correction term used by PhotoRoom Eq. (7). -/
noncomputable def blurForegroundCorrection (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter * blurMeanResidual ctx

/--
The idealized PhotoRoom foreground update
`\hat F_i + α_i (I_i - α_i \hat F_i - (1-α_i)\hat B_i)`.
-/
noncomputable def blurFusionForeground (ctx : LocalContext ι) : ℝ :=
  blurForegroundMean ctx + blurForegroundCorrection ctx

/--
The local Blur-Fusion output pair.

The foreground is corrected by Eq. (7), while the background keeps the stage-one mean value,
matching the quantity threaded into the next pass of the PhotoRoom implementation.
-/
noncomputable def blurFusionOutput (ctx : LocalContext ι) : LocalUnknown :=
  mkLocalUnknown (blurFusionForeground ctx) (blurBackgroundMean ctx)

@[simp] theorem blurForegroundWeightSum_eq_sum_alphaNeighbor (ctx : LocalContext ι) :
    blurForegroundWeightSum ctx = ∑ j, ctx.alphaNeighbor j := rfl

@[simp] theorem blurBackgroundWeightSum_eq_sum_one_sub_alphaNeighbor (ctx : LocalContext ι) :
    blurBackgroundWeightSum ctx = ∑ j, (1 - ctx.alphaNeighbor j) := rfl

@[simp] theorem blurForegroundSum_eq_sum_alphaNeighbor_mul_fgNeighbor (ctx : LocalContext ι) :
    blurForegroundSum ctx = ∑ j, ctx.alphaNeighbor j * ctx.fgNeighbor j := rfl

@[simp] theorem blurBackgroundSum_eq_sum_one_sub_alphaNeighbor_mul_bgNeighbor
    (ctx : LocalContext ι) :
    blurBackgroundSum ctx = ∑ j, (1 - ctx.alphaNeighbor j) * ctx.bgNeighbor j := rfl

@[simp] theorem foreground_blurFusionOutput (ctx : LocalContext ι) :
    foreground (blurFusionOutput ctx) = blurFusionForeground ctx := by
  simp [blurFusionOutput, foreground, mkLocalUnknown]

@[simp] theorem background_blurFusionOutput (ctx : LocalContext ι) :
    background (blurFusionOutput ctx) = blurBackgroundMean ctx := by
  simp [blurFusionOutput, background, mkLocalUnknown]

@[simp] theorem blurMeanResidual_eq
    (ctx : LocalContext ι) :
    blurMeanResidual ctx =
      ctx.imageValue -
        (ctx.alphaCenter * blurForegroundMean ctx +
          (1 - ctx.alphaCenter) * blurBackgroundMean ctx) := by
  simp [blurMeanResidual, FastMLFE2.Theory.Core.LocalContext.compositingValue_eq]

theorem blurFusionForeground_eq
    (ctx : LocalContext ι) :
    blurFusionForeground ctx =
      blurForegroundMean ctx +
        ctx.alphaCenter *
          (ctx.imageValue -
            (ctx.alphaCenter * blurForegroundMean ctx +
              (1 - ctx.alphaCenter) * blurBackgroundMean ctx)) := by
  rw [blurFusionForeground, blurForegroundCorrection, blurMeanResidual_eq]

theorem blurForegroundStageTwoCost_eq
    (ctx : LocalContext ι)
    (foregroundValue : ℝ) :
    blurForegroundStageTwoCost ctx foregroundValue =
      (ctx.alphaCenter * foregroundValue + (1 - ctx.alphaCenter) * blurBackgroundMean ctx -
          ctx.imageValue) ^ 2 +
        (foregroundValue - blurForegroundMean ctx) ^ 2 := rfl

end LocalContext

namespace LocalContextBuilder

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

/-- Pointwise Blur-Fusion update induced by the current pixel-state. -/
noncomputable def blurFusionUpdateAt
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ)
    (p : κ) : LocalUnknown :=
  LocalContext.blurFusionOutput (builder.build p state)

/-- One simultaneous Blur-Fusion pass over the whole pixel-state. -/
noncomputable def blurFusionStep
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ) : PixelState κ :=
  fun p => blurFusionUpdateAt builder state p

/-- `k` repeated Blur-Fusion passes. -/
noncomputable def blurFusionIterate
    (builder : LocalContextBuilder κ η)
    (k : Nat) : PixelState κ → PixelState κ :=
  Nat.iterate (blurFusionStep builder) k

/-- One Blur-Fusion pass, matching the paper's `x1` terminology. -/
noncomputable def blurFusionX1
    (builder : LocalContextBuilder κ η) : PixelState κ → PixelState κ :=
  blurFusionIterate builder 1

/-- Two Blur-Fusion passes, matching the paper's `x2` terminology. -/
noncomputable def blurFusionX2
    (builder : LocalContextBuilder κ η) : PixelState κ → PixelState κ :=
  blurFusionIterate builder 2

@[simp] theorem blurFusionUpdateAt_eq
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ)
    (p : κ) :
    blurFusionUpdateAt builder state p =
      LocalContext.blurFusionOutput (builder.build p state) := rfl

@[simp] theorem blurFusionStep_apply
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ)
    (p : κ) :
    blurFusionStep builder state p = blurFusionUpdateAt builder state p := rfl

@[simp] theorem blurFusionX1_eq_blurFusionStep
    (builder : LocalContextBuilder κ η) :
    blurFusionX1 builder = blurFusionStep builder := by
  funext state
  funext p
  simp [blurFusionX1, blurFusionIterate]

theorem blurFusionX2_eq_blurFusionStep_comp
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ) :
    blurFusionX2 builder state = blurFusionStep builder (blurFusionStep builder state) := by
  funext p
  simp [blurFusionX2, blurFusionIterate, Nat.iterate]

end LocalContextBuilder

end FastMLFE2.Theory.Approximation
