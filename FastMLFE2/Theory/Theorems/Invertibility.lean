import FastMLFE2.Theory.Assumptions.Bundles

namespace FastMLFE2.Theory.Theorems

/-!
Initial well-posedness theorems for the local theory kernel.
-/

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem neighborWeight_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] (j : ι) :
    0 ≤ ctx.neighborWeight j := by
  have hε : 0 ≤ ctx.epsilonR := le_of_lt (CoreMathAssumptions.epsilonPos (ctx := ctx))
  have hω : 0 ≤ ctx.omega := CoreMathAssumptions.omegaNonneg (ctx := ctx)
  have habs : 0 ≤ |ctx.alphaCenter - ctx.alphaNeighbor j| := abs_nonneg _
  exact add_nonneg hε (mul_nonneg hω habs)

theorem neighborWeight_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] (j : ι) :
    0 < ctx.neighborWeight j := by
  have hε : 0 < ctx.epsilonR := CoreMathAssumptions.epsilonPos (ctx := ctx)
  have hω : 0 ≤ ctx.omega := CoreMathAssumptions.omegaNonneg (ctx := ctx)
  have habs : 0 ≤ |ctx.alphaCenter - ctx.alphaNeighbor j| := abs_nonneg _
  exact add_pos_of_pos_of_nonneg hε (mul_nonneg hω habs)

theorem totalWeight_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.totalWeight := by
  classical
  let j : ι := Classical.choice (CoreMathAssumptions.neighborNonempty (ctx := ctx))
  have hj : j ∈ (Finset.univ : Finset ι) := by simp
  have hle : ctx.neighborWeight j ≤ ctx.totalWeight := by
    simpa only [LocalContext.totalWeight] using
      (Finset.single_le_sum (fun k _ => neighborWeight_nonneg ctx k) hj :
        ctx.neighborWeight j ≤ ∑ k, ctx.neighborWeight k)
  exact lt_of_lt_of_le (neighborWeight_pos ctx j) hle

theorem normalMatrix_det (ctx : LocalContext ι) :
    ctx.normalMatrix.det =
      ctx.totalWeight * (ctx.totalWeight + ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [LocalContext.normalMatrix]
  ring

theorem normalMatrix_det_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.normalMatrix.det := by
  rw [normalMatrix_det]
  have htotal : 0 < ctx.totalWeight := totalWeight_pos ctx
  have hsquares : 0 ≤ ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 := by positivity
  nlinarith

theorem normalMatrix_det_ne_zero (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.det ≠ 0 := by
  exact ne_of_gt (normalMatrix_det_pos ctx)

theorem normalMatrix_det_isUnit (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    IsUnit ctx.normalMatrix.det := by
  exact isUnit_iff_ne_zero.mpr (normalMatrix_det_ne_zero ctx)

end LocalContext

end FastMLFE2.Theory.Theorems
