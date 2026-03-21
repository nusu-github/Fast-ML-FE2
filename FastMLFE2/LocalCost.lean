import FastMLFE2.Compositing
import FastMLFE2.LinearAlgebra

namespace FastMLFE2

namespace LocalData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarCost (data : LocalData ι) (α image : ℝ) (g : FBVec) : ℝ :=
  (compositingResidual α image g) ^ 2 +
    ∑ j, data.weights j *
      ((foreground g - data.fgNeighbors j) ^ 2 + (background g - data.bgNeighbors j) ^ 2)

def matrixCost (data : LocalData ι) (α image : ℝ) (g : FBVec) : ℝ :=
  (compositingResidual α image g) ^ 2 +
    dotProduct (data.neighborResidual g) (data.weightMatrix.mulVec (data.neighborResidual g))

theorem matrixNeighborTerm_eq (data : LocalData ι) (g : FBVec) :
    dotProduct (data.neighborResidual g) (data.weightMatrix.mulVec (data.neighborResidual g)) =
      ∑ j, data.weights j *
        ((foreground g - data.fgNeighbors j) ^ 2 + (background g - data.bgNeighbors j) ^ 2) := by
  simp only [dotProduct, Fintype.sum_sum_type, weightMatrix_mulVec_apply,
    neighborResidual_inl, neighborResidual_inr, weightVec_inl, weightVec_inr, pow_two]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  ring_nf

theorem matrixCost_eq_scalarCost (data : LocalData ι) (α image : ℝ) (g : FBVec) :
    data.matrixCost α image g = data.scalarCost α image g := by
  rw [matrixCost, scalarCost, matrixNeighborTerm_eq]

end LocalData

end FastMLFE2
