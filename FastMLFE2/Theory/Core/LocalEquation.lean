import Mathlib

namespace FastMLFE2.Theory.Core

/-!
Foundational local-equation definitions for the theory-first refoundation.
-/

abbrev LocalIdx := Fin 2

/-- A local unknown `(F_i^c, B_i^c)` for one pixel and one color channel. -/
abbrev LocalUnknown := LocalIdx → ℝ

def mkLocalUnknown (foreground background : ℝ) : LocalUnknown := ![foreground, background]

def foreground (g : LocalUnknown) : ℝ := g 0

def background (g : LocalUnknown) : ℝ := g 1

/-- The compositing weights `[alpha_i, 1 - alpha_i]`. -/
def uVec (alphaCenter : ℝ) : LocalUnknown := ![alphaCenter, 1 - alphaCenter]

@[simp] theorem foreground_mkLocalUnknown (f b : ℝ) :
    foreground (mkLocalUnknown f b) = f := by
  simp [foreground, mkLocalUnknown]

@[simp] theorem background_mkLocalUnknown (f b : ℝ) :
    background (mkLocalUnknown f b) = b := by
  simp [background, mkLocalUnknown]

@[simp] theorem foreground_uVec (alphaCenter : ℝ) :
    foreground (uVec alphaCenter) = alphaCenter := by
  simp [foreground, uVec]

@[simp] theorem background_uVec (alphaCenter : ℝ) :
    background (uVec alphaCenter) = 1 - alphaCenter := by
  simp [background, uVec]

/--
Raw local inputs for one pixel and one channel.

The key design point is that the refounded theory keeps `epsilonR`, `omega`, and neighbor
alphas as primitive data. The regularized weights are derived from them rather than assumed
as an opaque `weights : ι → ℝ`.
-/
structure LocalContext (ι : Type*) where
  alphaCenter : ℝ
  imageValue : ℝ
  alphaNeighbor : ι → ℝ
  fgNeighbor : ι → ℝ
  bgNeighbor : ι → ℝ
  epsilonR : ℝ
  omega : ℝ

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def neighborWeight (ctx : LocalContext ι) (j : ι) : ℝ :=
  ctx.epsilonR + ctx.omega * |ctx.alphaCenter - ctx.alphaNeighbor j|

def totalWeight (ctx : LocalContext ι) : ℝ :=
  ∑ j, ctx.neighborWeight j

def foregroundSum (ctx : LocalContext ι) : ℝ :=
  ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j

def backgroundSum (ctx : LocalContext ι) : ℝ :=
  ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j

def compositingValue (ctx : LocalContext ι) (g : LocalUnknown) : ℝ :=
  dotProduct (uVec ctx.alphaCenter) g

def compositingResidual (ctx : LocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.compositingValue g - ctx.imageValue

def localCost (ctx : LocalContext ι) (g : LocalUnknown) : ℝ :=
  ctx.compositingResidual g ^ 2 +
    ∑ j, ctx.neighborWeight j *
      ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)

/-- The reduced `2 x 2` normal matrix `U Uᵀ + Rᵀ V R`. -/
def normalMatrix (ctx : LocalContext ι) : Matrix LocalIdx LocalIdx ℝ :=
  ![![ctx.alphaCenter ^ 2 + ctx.totalWeight, ctx.alphaCenter * (1 - ctx.alphaCenter)],
    ![ctx.alphaCenter * (1 - ctx.alphaCenter), (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight]]

def rhs (ctx : LocalContext ι) : LocalUnknown :=
  ![
    ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum,
    (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum
  ]

omit [Fintype ι] in
@[simp] theorem compositingValue_eq (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.compositingValue g =
      ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g := by
  simp [compositingValue, uVec, foreground, background, dotProduct, Fin.sum_univ_two]

omit [Fintype ι] in
@[simp] theorem compositingResidual_eq (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.compositingResidual g =
      ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g - ctx.imageValue := by
  simp [compositingResidual, compositingValue_eq]

@[simp] theorem rhs_foreground (ctx : LocalContext ι) :
    foreground ctx.rhs = ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum := by
  simp [rhs, foreground]

@[simp] theorem rhs_background (ctx : LocalContext ι) :
    background ctx.rhs = (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum := by
  simp [rhs, background]

@[simp] theorem normalMatrix_mulVec_foreground (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.normalMatrix.mulVec g 0 =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight) * foreground g +
        ctx.alphaCenter * (1 - ctx.alphaCenter) * background g := by
  simpa [foreground, background] using
    (by simp [normalMatrix, Matrix.mulVec] : ctx.normalMatrix.mulVec g 0 =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight) * Matrix.vecHead g +
        ctx.alphaCenter * (1 - ctx.alphaCenter) * Matrix.vecHead (Matrix.vecTail g))

@[simp] theorem normalMatrix_mulVec_background (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.normalMatrix.mulVec g 1 =
      ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground g +
        ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * background g := by
  simpa [foreground, background] using
    (by simp [normalMatrix, Matrix.mulVec] : ctx.normalMatrix.mulVec g 1 =
      ctx.alphaCenter * (1 - ctx.alphaCenter) * Matrix.vecHead g +
        ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * Matrix.vecHead (Matrix.vecTail g))

end LocalContext

end FastMLFE2.Theory.Core
