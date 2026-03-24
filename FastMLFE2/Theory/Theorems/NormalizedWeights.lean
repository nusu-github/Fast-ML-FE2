import FastMLFE2.Theory.Core.LocalSemantics
import FastMLFE2.Theory.Theorems.Invertibility

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def normalizedWeight (ctx : LocalContext ι) (j : ι) : ℝ :=
  ctx.neighborWeight j / ctx.totalWeight

private theorem weightedSum_div_totalWeight_eq_sum_normalizedWeight_mul
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (x : ι → ℝ) :
    (∑ j, ctx.neighborWeight j * x j) / ctx.totalWeight =
      ∑ j, normalizedWeight ctx j * x j := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  calc
    (∑ j, ctx.neighborWeight j * x j) / ctx.totalWeight
        = ∑ j, (ctx.neighborWeight j * x j) / ctx.totalWeight := by
            simpa using
              (Finset.sum_div Finset.univ (fun j => ctx.neighborWeight j * x j) ctx.totalWeight)
    _ = ∑ j, normalizedWeight ctx j * x j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [normalizedWeight]
      field_simp [htw0]

theorem foregroundMean_eq_sum_normalizedWeight_mul
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    ctx.foregroundMean = ∑ j, normalizedWeight ctx j * ctx.fgNeighbor j := by
  rw [FastMLFE2.Theory.Core.LocalContext.foregroundMean,
    FastMLFE2.Theory.Core.LocalContext.foregroundSum_eq_sum_neighborWeight_mul]
  exact weightedSum_div_totalWeight_eq_sum_normalizedWeight_mul (ctx := ctx) ctx.fgNeighbor

theorem backgroundMean_eq_sum_normalizedWeight_mul
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    ctx.backgroundMean = ∑ j, normalizedWeight ctx j * ctx.bgNeighbor j := by
  rw [FastMLFE2.Theory.Core.LocalContext.backgroundMean,
    FastMLFE2.Theory.Core.LocalContext.backgroundSum_eq_sum_neighborWeight_mul]
  exact weightedSum_div_totalWeight_eq_sum_normalizedWeight_mul (ctx := ctx) ctx.bgNeighbor

theorem sum_normalizedWeight_eq_one
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    ∑ j, normalizedWeight ctx j = 1 := by
  have htw0 : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
  calc
    ∑ j, normalizedWeight ctx j
        = (∑ j, ctx.neighborWeight j) / ctx.totalWeight := by
            symm
            simpa [normalizedWeight] using
              (Finset.sum_div Finset.univ (fun j => ctx.neighborWeight j) ctx.totalWeight)
    _ = ctx.totalWeight / ctx.totalWeight := by
      rw [← FastMLFE2.Theory.Core.LocalContext.totalWeight_eq_sum_neighborWeight (ctx := ctx)]
    _ = 1 := by
      exact div_self htw0

end LocalContext

end FastMLFE2.Theory.Theorems
