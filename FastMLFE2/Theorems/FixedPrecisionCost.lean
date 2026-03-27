import FastMLFE2.FixedPrecision.Jacobi
import FastMLFE2.FixedPrecision.Cost
import FastMLFE2.Theorems.FixedPrecisionJacobi

namespace FastMLFE2.Theorems

open FastMLFE2.FixedPrecision

namespace FixedPrecision

open FixedLocalContext
open FixedLocalContextBuilder

variable {cfg : FixedFormat} {ι κ : Type*} [Fintype ι]
variable {η : κ → Type*} [∀ p, Fintype (η p)]

theorem decodedFullyFixedStep_eq_of_safety
    (ctx : FixedLocalContext cfg ι)
    (h : LocalSafetyCert ctx) :
    decodeUnknown cfg (ctx.fullyFixedMeanResidualStep) =
      decodeUnknown cfg (ctx.referenceFullyFixedStep) := by
  simpa using decodedFullyFixedStep_eq_reference_of_safety ctx h

theorem fullyFixedJacobiUpdateAt_eq_of_safety
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ)
    (h : LocalSafetyCert (builder.build p state)) :
    decodeUnknown cfg (builder.fullyFixedJacobiUpdateAt state p) =
      decodeUnknown cfg (FixedLocalContext.referenceFullyFixedStep (builder.build p state)) := by
  simpa [FixedLocalContextBuilder.fullyFixedJacobiUpdateAt] using
    decodedFullyFixedStep_eq_of_safety (builder.build p state) h

theorem localCost_nonneg
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι) :
    0 ≤ localStepCost model ctx := by
  exact localStepCost_nonneg model ctx

theorem jacobiCost_nonneg
    [Fintype κ]
    (model : WeightedCostModel)
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) :
    0 ≤ jacobiStepCost model builder state := by
  exact jacobiStepCost_nonneg model builder state

theorem fullyFixedLocalCost_le_reference
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι)
    (hLookup : model.weight .lookup + model.weight .shift ≤ model.weight .div)
    (hCompare : model.weight .compare ≤ model.weight .div) :
    localStepCost model ctx ≤ referenceLocalStepCost model ctx := by
  exact fullyFixed_local_cost_le_reference model ctx hLookup hCompare

theorem acceptable_of_referenceBudget
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι)
    (hBudget : coefficientErrorBudget cfg ≤ 1)
    (hLookup : model.weight .lookup + model.weight .shift ≤ model.weight .div)
    (hCompare : model.weight .compare ≤ model.weight .div) :
    AcceptableFixedFormat model ctx 1 (referenceLocalStepCost model ctx) := by
  refine ⟨hBudget, ?_⟩
  exact fullyFixedLocalCost_le_reference model ctx hLookup hCompare

theorem not_acceptable_of_small_error_budget
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι)
    (hBudget : 0 < coefficientErrorBudget cfg) :
    ¬ AcceptableFixedFormat model ctx 0 (referenceLocalStepCost model ctx) := by
  intro hAcc
  exact not_le_of_gt hBudget hAcc.1

theorem u8_coefficientErrorBudget_le_one :
    coefficientErrorBudget u8Format ≤ 1 := by
  norm_num [coefficientErrorBudget, coefficientQuantizationBudget, coeffScale, u8Format]

theorem u8_coefficientErrorBudget_pos :
    0 < coefficientErrorBudget u8Format := by
  norm_num [coefficientErrorBudget, coefficientQuantizationBudget, coeffScale, u8Format]

end FixedPrecision

end FastMLFE2.Theorems
