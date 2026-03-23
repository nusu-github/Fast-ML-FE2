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
    0 ≤ ctx.neighborWeight j :=
  add_nonneg
    (le_of_lt CoreMathAssumptions.epsilonPos)
    (mul_nonneg CoreMathAssumptions.omegaNonneg (abs_nonneg _))

theorem neighborWeight_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] (j : ι) :
    0 < ctx.neighborWeight j :=
  add_pos_of_pos_of_nonneg
    CoreMathAssumptions.epsilonPos
    (mul_nonneg CoreMathAssumptions.omegaNonneg (abs_nonneg _))

theorem totalWeight_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.totalWeight := by
  exact lt_of_lt_of_le
    (neighborWeight_pos ctx (Classical.choice (CoreMathAssumptions.neighborNonempty ctx)))
    (Finset.single_le_sum (fun k _ => neighborWeight_nonneg ctx k) (Finset.mem_univ _))

theorem normalMatrix_det (ctx : LocalContext ι) :
    ctx.normalMatrix.det =
      ctx.totalWeight * (ctx.totalWeight + ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) := by
  rw [Matrix.det_fin_two]; simp [LocalContext.normalMatrix]; ring

theorem normalMatrix_det_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.normalMatrix.det := by
  rw [normalMatrix_det]
  nlinarith [
    totalWeight_pos ctx,
    sq_nonneg ctx.alphaCenter,
    sq_nonneg (1 - ctx.alphaCenter)
  ]

theorem normalMatrix_det_ne_zero (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.det ≠ 0 :=
  (normalMatrix_det_pos ctx).ne'

theorem normalMatrix_det_isUnit (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    IsUnit ctx.normalMatrix.det :=
  isUnit_iff_ne_zero.mpr (normalMatrix_det_ne_zero ctx)

end LocalContext

end FastMLFE2.Theory.Theorems
