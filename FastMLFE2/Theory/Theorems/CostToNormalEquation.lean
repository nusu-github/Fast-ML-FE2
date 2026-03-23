import FastMLFE2.Theory.Core.LocalSemantics

namespace FastMLFE2.Theory.Theorems

/-!
Bridge the local cost to the normal-equation semantics via genuine derivatives.
-/

open FastMLFE2.Theory.Core

namespace LocalContext

variable {ι : Type*} [Fintype ι]

private theorem foreground_weightedDiff
    (ctx : LocalContext ι) (g : LocalUnknown) :
    (∑ j, ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j)) =
      ctx.totalWeight * foreground g - ctx.foregroundSum := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [LocalContext.totalWeight, LocalContext.foregroundSum]

private theorem background_weightedDiff
    (ctx : LocalContext ι) (g : LocalUnknown) :
    (∑ j, ctx.neighborWeight j * (background g - ctx.bgNeighbor j)) =
      ctx.totalWeight * background g - ctx.backgroundSum := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [LocalContext.totalWeight, LocalContext.backgroundSum]

private theorem foreground_neighborCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    (∑ j, ctx.neighborWeight j *
      ((foreground
          (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) - ctx.fgNeighbor j) ^ 2 +
        (background
          (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) - ctx.bgNeighbor j) ^ 2)) =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        t ^ 2 * ctx.totalWeight +
        2 * t * (ctx.totalWeight * foreground g - ctx.foregroundSum) := by
  calc
    ∑ j, ctx.neighborWeight j *
      ((foreground (LocalContext.perturbForeground g t) - ctx.fgNeighbor j) ^ 2 +
        (background (LocalContext.perturbForeground g t) - ctx.bgNeighbor j) ^ 2)
        = ∑ j,
        (ctx.neighborWeight j *
            ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) +
          2 * t * (ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j)) +
          t ^ 2 * ctx.neighborWeight j) := by
            refine Finset.sum_congr rfl fun j _ => ?_; simp; ring
    _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, foreground_weightedDiff]
          simp [LocalContext.totalWeight]; ring

private theorem background_neighborCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    (∑ j, ctx.neighborWeight j *
      ((foreground
          (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) - ctx.fgNeighbor j) ^ 2 +
        (background
          (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) - ctx.bgNeighbor j) ^ 2)) =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        t ^ 2 * ctx.totalWeight +
        2 * t * (ctx.totalWeight * background g - ctx.backgroundSum) := by
  calc
    ∑ j, ctx.neighborWeight j *
      ((foreground (LocalContext.perturbBackground g t) - ctx.fgNeighbor j) ^ 2 +
        (background (LocalContext.perturbBackground g t) - ctx.bgNeighbor j) ^ 2)
        = ∑ j,
        (ctx.neighborWeight j *
            ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) +
          2 * t * (ctx.neighborWeight j * (background g - ctx.bgNeighbor j)) +
          t ^ 2 * ctx.neighborWeight j) := by
            refine Finset.sum_congr rfl fun j _ => ?_; simp; ring
    _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, background_weightedDiff]
          simp [LocalContext.totalWeight]; ring

private theorem hasDerivAt_quadraticLine (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => c + t ^ 2 * a + 2 * t * b) (2 * b) 0 := by
  have hquad : HasDerivAt (fun t : ℝ => t ^ 2 * a) 0 0 := by
    simpa [pow_two, mul_assoc] using (((hasDerivAt_id 0).pow 2).mul_const a)
  have hlin : HasDerivAt (fun t : ℝ => 2 * (t * b)) (2 * b) 0 := by
    simpa [mul_assoc] using (HasDerivAt.const_mul 2 (hasDerivAt_mul_const (x := 0) b))
  convert (hasDerivAt_const 0 c).add (hquad.add hlin) using 1
  · funext t; simp; ring
  · ring

theorem foregroundLineCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    ctx.foregroundLineCost g t =
      ctx.localCost g +
      t ^ 2 * (ctx.alphaCenter ^ 2 + ctx.totalWeight) +
      2 * t * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0) := by
  rw [LocalContext.foregroundLineCost, LocalContext.localCost, foreground_neighborCost_expand]
  have hcomp :
      ctx.compositingResidual (LocalContext.perturbForeground g t) ^ 2 =
        ctx.compositingResidual g ^ 2 +
          t ^ 2 * ctx.alphaCenter ^ 2 +
          2 * t * (ctx.alphaCenter * ctx.compositingResidual g) := by
    simp [LocalContext.compositingResidual_eq, pow_two]; ring
  rw [hcomp]
  have hrhs : ctx.rhs 0 = ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum := by
    simp [LocalContext.rhs]
  have hfgsum : (∑ x, ctx.neighborWeight x * ctx.fgNeighbor x) = ctx.foregroundSum := by
    simp [LocalContext.foregroundSum]
  suffices hsimp :
      (ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g - ctx.imageValue) *
            ((ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g) -
              ctx.imageValue) +
          t * t * (ctx.alphaCenter * ctx.alphaCenter) +
        2 * t *
          (ctx.alphaCenter *
            ((ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g) -
              ctx.imageValue)) +
      ((∑ x,
            ctx.neighborWeight x *
              ((foreground g - ctx.fgNeighbor x) * (foreground g - ctx.fgNeighbor x) +
                (background g - ctx.bgNeighbor x) * (background g - ctx.bgNeighbor x))) +
          t * t * ∑ j, ctx.neighborWeight j +
        2 * t *
          ((∑ j, ctx.neighborWeight j) * foreground g -
            ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j)) =
        (ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g - ctx.imageValue) *
              ((ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g) -
                ctx.imageValue) +
            ∑ x,
              ctx.neighborWeight x *
                ((foreground g - ctx.fgNeighbor x) * (foreground g - ctx.fgNeighbor x) +
                  (background g - ctx.bgNeighbor x) * (background g - ctx.bgNeighbor x)) +
          t * t * (ctx.alphaCenter * ctx.alphaCenter + ∑ j, ctx.neighborWeight j) +
        2 * t *
          ((ctx.alphaCenter * ctx.alphaCenter + ∑ j, ctx.neighborWeight j) * foreground g +
            ctx.alphaCenter * (1 - ctx.alphaCenter) * background g -
            ctx.rhs 0) by
    rw [hrhs, hfgsum] at hsimp
    simpa [LocalContext.localCost, LocalContext.compositingResidual_eq,
      LocalContext.normalMatrix_mulVec_foreground, pow_two] using hsimp
  rw [hrhs, hfgsum]; ring

theorem backgroundLineCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    ctx.backgroundLineCost g t =
      ctx.localCost g +
      t ^ 2 * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) +
      2 * t * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1) := by
  rw [LocalContext.backgroundLineCost, LocalContext.localCost, background_neighborCost_expand]
  have hcomp :
      ctx.compositingResidual (LocalContext.perturbBackground g t) ^ 2 =
        ctx.compositingResidual g ^ 2 +
          t ^ 2 * (1 - ctx.alphaCenter) ^ 2 +
          2 * t * ((1 - ctx.alphaCenter) * ctx.compositingResidual g) := by
    simp [LocalContext.compositingResidual_eq, pow_two]; ring
  rw [hcomp]
  have hrhs : ctx.rhs 1 = (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum := by
    simp [LocalContext.rhs]
  have hbgsum : (∑ x, ctx.neighborWeight x * ctx.bgNeighbor x) = ctx.backgroundSum := by
    simp [LocalContext.backgroundSum]
  suffices hsimp :
      (ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g - ctx.imageValue) *
            ((ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g) -
              ctx.imageValue) +
          t * t * ((1 - ctx.alphaCenter) * (1 - ctx.alphaCenter)) +
        2 * t *
          ((1 - ctx.alphaCenter) *
            ((ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g) -
              ctx.imageValue)) +
      ((∑ x,
            ctx.neighborWeight x *
              ((foreground g - ctx.fgNeighbor x) * (foreground g - ctx.fgNeighbor x) +
                (background g - ctx.bgNeighbor x) * (background g - ctx.bgNeighbor x))) +
          t * t * ∑ j, ctx.neighborWeight j +
        2 * t *
          ((∑ j, ctx.neighborWeight j) * background g -
            ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j)) =
        (ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g - ctx.imageValue) *
              ((ctx.alphaCenter * foreground g + (1 - ctx.alphaCenter) * background g) -
                ctx.imageValue) +
            ∑ x,
              ctx.neighborWeight x *
                ((foreground g - ctx.fgNeighbor x) * (foreground g - ctx.fgNeighbor x) +
                  (background g - ctx.bgNeighbor x) * (background g - ctx.bgNeighbor x)) +
          t * t * ((1 - ctx.alphaCenter) * (1 - ctx.alphaCenter) + ∑ j, ctx.neighborWeight j) +
        2 * t *
          (ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground g +
            (((1 - ctx.alphaCenter) * (1 - ctx.alphaCenter) + ∑ j, ctx.neighborWeight j) *
              background g) -
            ctx.rhs 1) by
    rw [hrhs, hbgsum] at hsimp
    simpa [LocalContext.localCost, LocalContext.compositingResidual_eq,
      LocalContext.normalMatrix_mulVec_background, pow_two] using hsimp
  rw [hrhs, hbgsum]; ring

theorem hasDerivAt_foregroundLineCost
    (ctx : LocalContext ι) (g : LocalUnknown) :
    HasDerivAt (fun t : ℝ => ctx.foregroundLineCost g t)
      (2 * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0)) 0 := by
  rw [show (fun t => ctx.foregroundLineCost g t) =
      fun t => ctx.localCost g + t ^ 2 * _ + 2 * t * _
      from funext (foregroundLineCost_expand ctx g)]
  exact hasDerivAt_quadraticLine _ _ _

theorem hasDerivAt_backgroundLineCost
    (ctx : LocalContext ι) (g : LocalUnknown) :
    HasDerivAt (fun t : ℝ => ctx.backgroundLineCost g t)
      (2 * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1)) 0 := by
  rw [show (fun t => ctx.backgroundLineCost g t) =
      fun t => ctx.localCost g + t ^ 2 * _ + 2 * t * _
      from funext (backgroundLineCost_expand ctx g)]
  exact hasDerivAt_quadraticLine _ _ _

theorem isCostStationary_iff_solvesNormalEquation
    (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.IsCostStationary g ↔ ctx.SolvesNormalEquation g := by
  constructor
  · intro ⟨hfg0, hbg0⟩
    have hfg := HasDerivAt.unique (hasDerivAt_foregroundLineCost ctx g) hfg0
    have hbg := HasDerivAt.unique (hasDerivAt_backgroundLineCost ctx g) hbg0
    have hfgEq : ctx.normalMatrix.mulVec g 0 = ctx.rhs 0 := by nlinarith
    have hbgEq : ctx.normalMatrix.mulVec g 1 = ctx.rhs 1 := by nlinarith
    funext i; fin_cases i
    · exact hfgEq
    · exact hbgEq
  · intro hsolve
    constructor
    · simpa [congrFun hsolve 0] using hasDerivAt_foregroundLineCost ctx g
    · simpa [congrFun hsolve 1] using hasDerivAt_backgroundLineCost ctx g

end LocalContext

end FastMLFE2.Theory.Theorems
