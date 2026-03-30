import FastMLFE2.Core.LocalEquation

namespace FastMLFE2.Core

/-!
Absolute-anchor variant of the local FMFE equation.

This sibling semantics preserves the original relative smoothness terms and adds quadratic
Tikhonov anchoring terms for the foreground/background unknowns.
-/

structure AnchoredLocalContext (ι : Type*) where
  alphaCenter : ℝ
  imageValue : ℝ
  alphaNeighbor : ι → ℝ
  fgNeighbor : ι → ℝ
  bgNeighbor : ι → ℝ
  epsilonR : ℝ
  omega : ℝ
  fgPrior : ℝ
  bgPrior : ℝ
  fgAnchorWeight : ℝ
  bgAnchorWeight : ℝ

namespace AnchoredLocalContext

variable {ι : Type*} [Fintype ι]

def toLocalContext (ctx : AnchoredLocalContext ι) : LocalContext ι where
  alphaCenter := ctx.alphaCenter
  imageValue := ctx.imageValue
  alphaNeighbor := ctx.alphaNeighbor
  fgNeighbor := ctx.fgNeighbor
  bgNeighbor := ctx.bgNeighbor
  epsilonR := ctx.epsilonR
  omega := ctx.omega

def neighborWeight (ctx : AnchoredLocalContext ι) (j : ι) : ℝ :=
  ctx.toLocalContext.neighborWeight j

def totalWeight (ctx : AnchoredLocalContext ι) : ℝ :=
  ctx.toLocalContext.totalWeight

def foregroundSum (ctx : AnchoredLocalContext ι) : ℝ :=
  ctx.toLocalContext.foregroundSum

def backgroundSum (ctx : AnchoredLocalContext ι) : ℝ :=
  ctx.toLocalContext.backgroundSum

def compositingValue (ctx : AnchoredLocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.toLocalContext.compositingValue g

def compositingResidual (ctx : AnchoredLocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.toLocalContext.compositingResidual g

def localCost (ctx : AnchoredLocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.toLocalContext.localCost g +
    ctx.fgAnchorWeight * (foreground g - ctx.fgPrior) ^ 2 +
    ctx.bgAnchorWeight * (background g - ctx.bgPrior) ^ 2

def anchorDiagMatrix (ctx : AnchoredLocalContext ι) : Matrix LocalIdx LocalIdx ℝ :=
  ![![ctx.fgAnchorWeight, 0], ![0, ctx.bgAnchorWeight]]

def normalMatrix (ctx : AnchoredLocalContext ι) : Matrix LocalIdx LocalIdx ℝ :=
  ![![ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight,
      ctx.alphaCenter * (1 - ctx.alphaCenter)],
    ![ctx.alphaCenter * (1 - ctx.alphaCenter),
      (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight]]

def rhs (ctx : AnchoredLocalContext ι) : LocalUnknown :=
  ![
    ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior,
    (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior
  ]

def SolvesNormalEquation (ctx : AnchoredLocalContext ι) (g : LocalUnknown) : Prop :=
  ctx.normalMatrix.mulVec g = ctx.rhs

@[simp] theorem toLocalContext_alphaCenter (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.alphaCenter = ctx.alphaCenter := rfl

@[simp] theorem toLocalContext_imageValue (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.imageValue = ctx.imageValue := rfl

@[simp] theorem toLocalContext_alphaNeighbor (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.alphaNeighbor = ctx.alphaNeighbor := rfl

@[simp] theorem toLocalContext_fgNeighbor (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.fgNeighbor = ctx.fgNeighbor := rfl

@[simp] theorem toLocalContext_bgNeighbor (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.bgNeighbor = ctx.bgNeighbor := rfl

@[simp] theorem toLocalContext_epsilonR (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.epsilonR = ctx.epsilonR := rfl

@[simp] theorem toLocalContext_omega (ctx : AnchoredLocalContext ι) :
    ctx.toLocalContext.omega = ctx.omega := rfl

@[simp] theorem neighborWeight_eq (ctx : AnchoredLocalContext ι) (j : ι) :
    ctx.neighborWeight j = ctx.epsilonR + ctx.omega * |ctx.alphaCenter - ctx.alphaNeighbor j| := by
  rfl

@[simp] theorem totalWeight_eq (ctx : AnchoredLocalContext ι) :
    ctx.totalWeight = ∑ j, ctx.neighborWeight j := rfl

@[simp] theorem foregroundSum_eq (ctx : AnchoredLocalContext ι) :
    ctx.foregroundSum = ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j := rfl

@[simp] theorem backgroundSum_eq (ctx : AnchoredLocalContext ι) :
    ctx.backgroundSum = ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j := rfl

@[simp] theorem compositingValue_eq (ctx : AnchoredLocalContext ι) (g : LocalUnknown) :
    ctx.compositingValue g =
      ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g := by
  simp [compositingValue, LocalContext.compositingValue_eq]

@[simp] theorem compositingResidual_eq (ctx : AnchoredLocalContext ι) (g : LocalUnknown) :
    ctx.compositingResidual g =
      ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g - ctx.imageValue := by
  simp [compositingResidual]

theorem normalMatrix_eq_base_add_diag (ctx : AnchoredLocalContext ι) :
    ctx.normalMatrix =
      ctx.toLocalContext.normalMatrix + ctx.anchorDiagMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalMatrix, anchorDiagMatrix, LocalContext.normalMatrix, totalWeight]

@[simp] theorem rhs_eq_base_add_anchor (ctx : AnchoredLocalContext ι) :
    ctx.rhs =
      ctx.toLocalContext.rhs +
        mkLocalUnknown (ctx.fgAnchorWeight * ctx.fgPrior) (ctx.bgAnchorWeight * ctx.bgPrior) := by
  ext i
  fin_cases i <;>
    simp [rhs, LocalContext.rhs, mkLocalUnknown, foregroundSum, backgroundSum]

@[simp] theorem localCost_eq_base_add_anchor (ctx : AnchoredLocalContext ι) :
    ctx.localCost =
      fun g =>
        ctx.toLocalContext.localCost g +
          ctx.fgAnchorWeight * (foreground g - ctx.fgPrior) ^ 2 +
          ctx.bgAnchorWeight * (background g - ctx.bgPrior) ^ 2 := rfl

@[simp] theorem foreground_rhs (ctx : AnchoredLocalContext ι) :
    foreground ctx.rhs =
      ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum + ctx.fgAnchorWeight * ctx.fgPrior := by
  simp [rhs, foreground]

@[simp] theorem background_rhs (ctx : AnchoredLocalContext ι) :
    background ctx.rhs =
      (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum + ctx.bgAnchorWeight * ctx.bgPrior := by
  simp [rhs, background]

@[simp] theorem normalMatrix_mulVec_foreground
    (ctx : AnchoredLocalContext ι) (g : LocalUnknown) :
    ctx.normalMatrix.mulVec g 0 =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) * foreground g +
        ctx.alphaCenter * (1 - ctx.alphaCenter) * background g := by
  simpa [foreground, background] using
    (by simp [normalMatrix, Matrix.mulVec] : ctx.normalMatrix.mulVec g 0 =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) * Matrix.vecHead g +
        ctx.alphaCenter * (1 - ctx.alphaCenter) * Matrix.vecHead (Matrix.vecTail g))

@[simp] theorem normalMatrix_mulVec_background
    (ctx : AnchoredLocalContext ι) (g : LocalUnknown) :
    ctx.normalMatrix.mulVec g 1 =
      ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground g +
        ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) * background g := by
  simpa [foreground, background] using
    (by simp [normalMatrix, Matrix.mulVec] : ctx.normalMatrix.mulVec g 1 =
      ctx.alphaCenter * (1 - ctx.alphaCenter) * Matrix.vecHead g +
        ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) *
          Matrix.vecHead (Matrix.vecTail g))

end AnchoredLocalContext

end FastMLFE2.Core
