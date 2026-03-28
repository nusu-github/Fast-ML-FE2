import FastMLFE2.Core.LocalSemantics
import FastMLFE2.Theorems.Solvability.Invertibility

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def normalizedWeight (ctx : LocalContext ι) (j : ι) : ℝ :=
  ctx.neighborWeight j / ctx.totalWeight

private theorem weightedSum_div_totalWeight_eq_sum_normalizedWeight_mul
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (x : ι → ℝ) :
    (∑ j, ctx.neighborWeight j * x j) / ctx.totalWeight =
      ∑ j, normalizedWeight ctx j * x j := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  simp_rw [normalizedWeight, div_mul_eq_mul_div]
  rw [← Finset.sum_div]

theorem foregroundMean_eq_sum_normalizedWeight_mul
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.foregroundMean = ∑ j, normalizedWeight ctx j * ctx.fgNeighbor j := by
  rw [LocalContext.foregroundMean, LocalContext.foregroundSum_eq_sum_neighborWeight_mul]
  exact weightedSum_div_totalWeight_eq_sum_normalizedWeight_mul ctx ctx.fgNeighbor

theorem backgroundMean_eq_sum_normalizedWeight_mul
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.backgroundMean = ∑ j, normalizedWeight ctx j * ctx.bgNeighbor j := by
  rw [LocalContext.backgroundMean, LocalContext.backgroundSum_eq_sum_neighborWeight_mul]
  exact weightedSum_div_totalWeight_eq_sum_normalizedWeight_mul ctx ctx.bgNeighbor

theorem sum_normalizedWeight_eq_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ∑ j, normalizedWeight ctx j = 1 := by
  simp_rw [normalizedWeight, ← Finset.sum_div,
    LocalContext.totalWeight_eq_sum_neighborWeight]
  exact div_self (totalWeight_pos ctx).ne'

end LocalContext

end FastMLFE2.Theorems
