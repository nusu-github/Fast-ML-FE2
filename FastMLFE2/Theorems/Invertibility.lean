import FastMLFE2.Assumptions.Bundles

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem neighborWeight_nonneg (ctx : LocalContext ι) [CoreMathAssumptions ctx] (j : ι) :
    0 ≤ ctx.neighborWeight j :=
  add_nonneg CoreMathAssumptions.epsilonPos.le
    (mul_nonneg CoreMathAssumptions.omegaNonneg (abs_nonneg _))

theorem neighborWeight_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] (j : ι) :
    0 < ctx.neighborWeight j :=
  add_pos_of_pos_of_nonneg CoreMathAssumptions.epsilonPos
    (mul_nonneg CoreMathAssumptions.omegaNonneg (abs_nonneg _))

theorem totalWeight_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.totalWeight :=
  (neighborWeight_pos ctx (Classical.choice (CoreMathAssumptions.neighborNonempty ctx))).trans_le
    (Finset.single_le_sum (fun k _ => neighborWeight_nonneg ctx k) (Finset.mem_univ _))

theorem weightedMeanDenom_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.weightedMeanDenom := by
  simp [LocalContext.weightedMeanDenom, add_assoc]
  linarith [totalWeight_pos ctx, sq_nonneg ctx.alphaCenter, sq_nonneg (1 - ctx.alphaCenter)]

theorem normalMatrix_det (ctx : LocalContext ι) :
    ctx.normalMatrix.det = ctx.totalWeight * ctx.weightedMeanDenom := by
  rw [Matrix.det_fin_two]; simp [LocalContext.normalMatrix, LocalContext.weightedMeanDenom]; ring

theorem normalMatrix_det_pos (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.normalMatrix.det := by
  rw [normalMatrix_det]; exact mul_pos (totalWeight_pos ctx) (weightedMeanDenom_pos ctx)

theorem normalMatrix_det_ne_zero (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.normalMatrix.det ≠ 0 := (normalMatrix_det_pos ctx).ne'

theorem normalMatrix_det_isUnit (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    IsUnit ctx.normalMatrix.det := isUnit_iff_ne_zero.mpr (normalMatrix_det_ne_zero ctx)

end LocalContext

end FastMLFE2.Theorems
