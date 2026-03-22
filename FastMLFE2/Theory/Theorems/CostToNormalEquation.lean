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
  calc
    ∑ j, ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j)
        = ∑ j, (ctx.neighborWeight j * foreground g - ctx.neighborWeight j * ctx.fgNeighbor j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
    _ = (∑ j, ctx.neighborWeight j * foreground g) - ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j := by
          rw [Finset.sum_sub_distrib]
    _ = foreground g * (∑ j, ctx.neighborWeight j) - ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j := by
          congr 1
          calc
            ∑ j, ctx.neighborWeight j * foreground g = ∑ j, foreground g * ctx.neighborWeight j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
            _ = foreground g * ∑ j, ctx.neighborWeight j := by
              symm
              exact Finset.mul_sum Finset.univ (fun j => ctx.neighborWeight j) (foreground g)
    _ = ctx.totalWeight * foreground g - ctx.foregroundSum := by
          simp [FastMLFE2.Theory.Core.LocalContext.totalWeight,
            FastMLFE2.Theory.Core.LocalContext.foregroundSum]
          ring

private theorem background_weightedDiff
    (ctx : LocalContext ι) (g : LocalUnknown) :
    (∑ j, ctx.neighborWeight j * (background g - ctx.bgNeighbor j)) =
      ctx.totalWeight * background g - ctx.backgroundSum := by
  calc
    ∑ j, ctx.neighborWeight j * (background g - ctx.bgNeighbor j)
        = ∑ j, (ctx.neighborWeight j * background g - ctx.neighborWeight j * ctx.bgNeighbor j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
    _ = (∑ j, ctx.neighborWeight j * background g) - ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j := by
          rw [Finset.sum_sub_distrib]
    _ = background g * (∑ j, ctx.neighborWeight j) - ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j := by
          congr 1
          calc
            ∑ j, ctx.neighborWeight j * background g = ∑ j, background g * ctx.neighborWeight j := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
            _ = background g * ∑ j, ctx.neighborWeight j := by
              symm
              exact Finset.mul_sum Finset.univ (fun j => ctx.neighborWeight j) (background g)
    _ = ctx.totalWeight * background g - ctx.backgroundSum := by
          simp [FastMLFE2.Theory.Core.LocalContext.totalWeight,
            FastMLFE2.Theory.Core.LocalContext.backgroundSum]
          ring

private theorem foreground_neighborCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    (∑ j, ctx.neighborWeight j *
      ((foreground (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) - ctx.fgNeighbor j) ^ 2 +
        (background (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) - ctx.bgNeighbor j) ^ 2)) =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        t ^ 2 * ctx.totalWeight +
        2 * t * (ctx.totalWeight * foreground g - ctx.foregroundSum) := by
  calc
    ∑ j, ctx.neighborWeight j *
      ((foreground (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) - ctx.fgNeighbor j) ^ 2 +
        (background (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) - ctx.bgNeighbor j) ^ 2)
        =
      ∑ j,
        (ctx.neighborWeight j *
            ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) +
          2 * t * (ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j)) +
          t ^ 2 * ctx.neighborWeight j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp
            ring
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        (∑ j, 2 * t * (ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j))) +
        (∑ j, t ^ 2 * ctx.neighborWeight j) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        2 * t * (∑ j, ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j)) +
        t ^ 2 * (∑ j, ctx.neighborWeight j) := by
          congr 2
          · symm
            exact Finset.mul_sum Finset.univ
              (fun j => ctx.neighborWeight j * (foreground g - ctx.fgNeighbor j)) (2 * t)
          · symm
            exact Finset.mul_sum Finset.univ (fun j => ctx.neighborWeight j) (t ^ 2)
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        2 * t * (ctx.totalWeight * foreground g - ctx.foregroundSum) +
        t ^ 2 * ctx.totalWeight := by
          rw [foreground_weightedDiff]
          simp [FastMLFE2.Theory.Core.LocalContext.totalWeight]
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        t ^ 2 * ctx.totalWeight +
        2 * t * (ctx.totalWeight * foreground g - ctx.foregroundSum) := by
          ring

private theorem background_neighborCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    (∑ j, ctx.neighborWeight j *
      ((foreground (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) - ctx.fgNeighbor j) ^ 2 +
        (background (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) - ctx.bgNeighbor j) ^ 2)) =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        t ^ 2 * ctx.totalWeight +
        2 * t * (ctx.totalWeight * background g - ctx.backgroundSum) := by
  calc
    ∑ j, ctx.neighborWeight j *
      ((foreground (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) - ctx.fgNeighbor j) ^ 2 +
        (background (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) - ctx.bgNeighbor j) ^ 2)
        =
      ∑ j,
        (ctx.neighborWeight j *
            ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) +
          2 * t * (ctx.neighborWeight j * (background g - ctx.bgNeighbor j)) +
          t ^ 2 * ctx.neighborWeight j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simp
            ring
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        (∑ j, 2 * t * (ctx.neighborWeight j * (background g - ctx.bgNeighbor j))) +
        (∑ j, t ^ 2 * ctx.neighborWeight j) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        2 * t * (∑ j, ctx.neighborWeight j * (background g - ctx.bgNeighbor j)) +
        t ^ 2 * (∑ j, ctx.neighborWeight j) := by
          congr 2
          · symm
            exact Finset.mul_sum Finset.univ
              (fun j => ctx.neighborWeight j * (background g - ctx.bgNeighbor j)) (2 * t)
          · symm
            exact Finset.mul_sum Finset.univ (fun j => ctx.neighborWeight j) (t ^ 2)
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        2 * t * (ctx.totalWeight * background g - ctx.backgroundSum) +
        t ^ 2 * ctx.totalWeight := by
          rw [background_weightedDiff]
          simp [FastMLFE2.Theory.Core.LocalContext.totalWeight]
    _ =
      (∑ j, ctx.neighborWeight j *
        ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2)) +
        t ^ 2 * ctx.totalWeight +
        2 * t * (ctx.totalWeight * background g - ctx.backgroundSum) := by
          ring

private theorem hasDerivAt_quadraticLine (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => c + t ^ 2 * a + 2 * t * b) (2 * b) 0 := by
  have hquad : HasDerivAt (fun t : ℝ => t ^ 2 * a) 0 0 := by
    simpa [pow_two, mul_assoc] using (((hasDerivAt_id 0).pow 2).mul_const a)
  have hlin : HasDerivAt (fun t : ℝ => 2 * (t * b)) (2 * b) 0 := by
    simpa [mul_assoc] using
      (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_mul_const (x := 0) b))
  convert (hasDerivAt_const 0 c).add (hquad.add hlin) using 1
  · funext t
    simp
    ring
  · ring

theorem foregroundLineCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    ctx.foregroundLineCost g t =
      ctx.localCost g +
      t ^ 2 * (ctx.alphaCenter ^ 2 + ctx.totalWeight) +
      2 * t * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0) := by
  rw [FastMLFE2.Theory.Core.LocalContext.foregroundLineCost,
    FastMLFE2.Theory.Core.LocalContext.localCost]
  rw [foreground_neighborCost_expand]
  have hcomp :
      ctx.compositingResidual (FastMLFE2.Theory.Core.LocalContext.perturbForeground g t) ^ 2 =
        ctx.compositingResidual g ^ 2 +
          t ^ 2 * ctx.alphaCenter ^ 2 +
          2 * t * (ctx.alphaCenter * ctx.compositingResidual g) := by
    simp [FastMLFE2.Theory.Core.LocalContext.compositingResidual_eq, pow_two]
    ring
  rw [hcomp]
  have hrhs : ctx.rhs 0 = ctx.alphaCenter * ctx.imageValue + ctx.foregroundSum := by
    simp [FastMLFE2.Theory.Core.LocalContext.rhs]
  have hfgsum : (∑ x, ctx.neighborWeight x * ctx.fgNeighbor x) = ctx.foregroundSum := by
    simp [FastMLFE2.Theory.Core.LocalContext.foregroundSum]
  simp [FastMLFE2.Theory.Core.LocalContext.localCost,
    FastMLFE2.Theory.Core.LocalContext.compositingResidual_eq,
    FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_foreground,
    pow_two]
  rw [hrhs, hfgsum]
  ring

theorem backgroundLineCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    ctx.backgroundLineCost g t =
      ctx.localCost g +
      t ^ 2 * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) +
      2 * t * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1) := by
  rw [FastMLFE2.Theory.Core.LocalContext.backgroundLineCost,
    FastMLFE2.Theory.Core.LocalContext.localCost]
  rw [background_neighborCost_expand]
  have hcomp :
      ctx.compositingResidual (FastMLFE2.Theory.Core.LocalContext.perturbBackground g t) ^ 2 =
        ctx.compositingResidual g ^ 2 +
          t ^ 2 * (1 - ctx.alphaCenter) ^ 2 +
          2 * t * ((1 - ctx.alphaCenter) * ctx.compositingResidual g) := by
    simp [FastMLFE2.Theory.Core.LocalContext.compositingResidual_eq, pow_two]
    ring
  rw [hcomp]
  have hrhs : ctx.rhs 1 = (1 - ctx.alphaCenter) * ctx.imageValue + ctx.backgroundSum := by
    simp [FastMLFE2.Theory.Core.LocalContext.rhs]
  have hbgsum : (∑ x, ctx.neighborWeight x * ctx.bgNeighbor x) = ctx.backgroundSum := by
    simp [FastMLFE2.Theory.Core.LocalContext.backgroundSum]
  simp [FastMLFE2.Theory.Core.LocalContext.localCost,
    FastMLFE2.Theory.Core.LocalContext.compositingResidual_eq,
    FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_background,
    pow_two]
  rw [hrhs, hbgsum]
  ring

theorem hasDerivAt_foregroundLineCost
    (ctx : LocalContext ι) (g : LocalUnknown) :
    HasDerivAt (fun t : ℝ => ctx.foregroundLineCost g t)
      (2 * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0)) 0 := by
  have hEq :
      (fun t : ℝ => ctx.foregroundLineCost g t) =
        fun t : ℝ =>
          ctx.localCost g +
            t ^ 2 * (ctx.alphaCenter ^ 2 + ctx.totalWeight) +
            2 * t * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0) := by
    funext t
    exact foregroundLineCost_expand ctx g t
  rw [hEq]
  exact hasDerivAt_quadraticLine
    (ctx.alphaCenter ^ 2 + ctx.totalWeight)
    (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0)
    (ctx.localCost g)

theorem hasDerivAt_backgroundLineCost
    (ctx : LocalContext ι) (g : LocalUnknown) :
    HasDerivAt (fun t : ℝ => ctx.backgroundLineCost g t)
      (2 * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1)) 0 := by
  have hEq :
      (fun t : ℝ => ctx.backgroundLineCost g t) =
        fun t : ℝ =>
          ctx.localCost g +
            t ^ 2 * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) +
            2 * t * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1) := by
    funext t
    exact backgroundLineCost_expand ctx g t
  rw [hEq]
  exact hasDerivAt_quadraticLine
    ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight)
    (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1)
    (ctx.localCost g)

end LocalContext

end FastMLFE2.Theory.Theorems
