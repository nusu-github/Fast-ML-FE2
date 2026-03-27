import FastMLFE2.FixedPrecision.Jacobi

namespace FastMLFE2.FixedPrecision

inductive WeightedOpKind where
  | add
  | sub
  | mul
  | div
  | shift
  | compare
  | lookup
  | clamp
  | quantize
  deriving DecidableEq, Repr

structure WeightedCostModel where
  weight : WeightedOpKind → ℚ
  nonneg : ∀ op, 0 ≤ weight op

namespace WeightedCostModel

def default : WeightedCostModel where
  weight
    | .add => 1
    | .sub => 1
    | .mul => 2
    | .div => 16
    | .shift => 1
    | .compare => 1
    | .lookup => 2
    | .clamp => 1
    | .quantize => 1
  nonneg := by
    intro op
    cases op <;> norm_num

end WeightedCostModel

def localStepCost
    {cfg : FixedFormat} {ι : Type*} [Fintype ι]
    (model : WeightedCostModel)
    (_ctx : FixedLocalContext cfg ι) : ℚ :=
  let n : ℚ := Fintype.card ι
  (4 * n + 5) * model.weight .add +
    3 * model.weight .sub +
    (2 * n + 6) * model.weight .mul +
    3 * model.weight .shift +
    2 * model.weight .lookup +
    2 * model.weight .compare +
    2 * model.weight .clamp +
    2 * model.weight .quantize

def referenceLocalStepCost
    {cfg : FixedFormat} {ι : Type*} [Fintype ι]
    (model : WeightedCostModel)
    (_ctx : FixedLocalContext cfg ι) : ℚ :=
  let n : ℚ := Fintype.card ι
  (4 * n + 7) * model.weight .add +
    3 * model.weight .sub +
    (2 * n + 8) * model.weight .mul +
    5 * model.weight .div +
    2 * model.weight .clamp +
    2 * model.weight .quantize

def jacobiStepCost
    {cfg : FixedFormat} {κ : Type*} [Fintype κ] {η : κ → Type*} [∀ p, Fintype (η p)]
    (model : WeightedCostModel)
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) : ℚ :=
  ∑ p, localStepCost model (builder.build p state)

def referenceJacobiStepCost
    {cfg : FixedFormat} {κ : Type*} [Fintype κ] {η : κ → Type*} [∀ p, Fintype (η p)]
    (model : WeightedCostModel)
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) : ℚ :=
  ∑ p, referenceLocalStepCost model (builder.build p state)

def coefficientErrorBudget (cfg : FixedFormat) : ℚ :=
  coefficientQuantizationBudget cfg + 1 / cfg.scale

def AcceptableFixedFormat
    {cfg : FixedFormat} {ι : Type*} [Fintype ι]
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι)
    (errorBudget referenceBudget : ℚ) : Prop :=
  coefficientErrorBudget cfg ≤ errorBudget ∧ localStepCost model ctx ≤ referenceBudget

theorem localStepCost_nonneg
    {cfg : FixedFormat} {ι : Type*} [Fintype ι]
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι) :
    0 ≤ localStepCost model ctx := by
  have h := model.nonneg
  simp [localStepCost]
  nlinarith [h .add, h .sub, h .mul, h .shift, h .lookup, h .compare, h .clamp, h .quantize]

theorem referenceLocalStepCost_nonneg
    {cfg : FixedFormat} {ι : Type*} [Fintype ι]
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι) :
    0 ≤ referenceLocalStepCost model ctx := by
  have h := model.nonneg
  simp [referenceLocalStepCost]
  nlinarith [h .add, h .sub, h .mul, h .div, h .clamp, h .quantize]

theorem jacobiStepCost_nonneg
    {cfg : FixedFormat} {κ : Type*} [Fintype κ] {η : κ → Type*} [∀ p, Fintype (η p)]
    (model : WeightedCostModel)
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) :
    0 ≤ jacobiStepCost model builder state := by
  classical
  refine Finset.sum_nonneg ?_
  intro p hp
  exact localStepCost_nonneg model (builder.build p state)

theorem coefficientErrorBudget_nonneg (cfg : FixedFormat) :
    0 ≤ coefficientErrorBudget cfg := by
  have hq : 0 ≤ coefficientQuantizationBudget cfg := coefficientQuantizationBudget_nonneg cfg
  have hs : 0 ≤ (1 : ℚ) / cfg.scale := by
    positivity
  simpa [coefficientErrorBudget] using add_nonneg hq hs

theorem fullyFixed_local_cost_le_reference
    {cfg : FixedFormat} {ι : Type*} [Fintype ι]
    (model : WeightedCostModel)
    (ctx : FixedLocalContext cfg ι)
    (hLookup : model.weight .lookup + model.weight .shift ≤ model.weight .div)
    (hCompare : model.weight .compare ≤ model.weight .div) :
    localStepCost model ctx ≤ referenceLocalStepCost model ctx := by
  have h0 := model.nonneg
  simp [localStepCost, referenceLocalStepCost]
  have hLookup3 : 2 * model.weight .lookup + 3 * model.weight .shift ≤ 3 * model.weight .div := by
    nlinarith [hLookup, h0 .lookup, h0 .shift, h0 .div]
  have hCompare2 : 2 * model.weight .compare ≤ 2 * model.weight .div := by
    nlinarith [hCompare]
  nlinarith [hLookup3, hCompare2, h0 .add, h0 .sub, h0 .mul, h0 .div, h0 .clamp, h0 .quantize]

end FastMLFE2.FixedPrecision
