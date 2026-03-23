import FastMLFE2.Theory.Level.Jacobi

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level
open FastMLFE2.Theory.Assumptions

namespace LocalContextBuilder

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

theorem jacobiStep_eq_closedForm
    (builder : LocalContextBuilder κ η) (state : PixelState κ) (p : κ) :
    builder.jacobiStep state p =
      LocalContext.closedFormSolution (builder.build p state) := rfl

theorem jacobiStep_solvesNormalEquation
    (builder : LocalContextBuilder κ η) (state : PixelState κ) (p : κ)
    [CoreMathAssumptions (builder.build p state)] :
    (builder.build p state).SolvesNormalEquation (builder.jacobiStep state p) := by
  simpa [LocalContextBuilder.jacobiStep, LocalContextBuilder.jacobiUpdateAt] using
    FastMLFE2.Theory.Theorems.LocalContext.closedForm_solvesNormalEquation (builder.build p state)

theorem jacobiStep_isCostStationary
    (builder : LocalContextBuilder κ η) (state : PixelState κ) (p : κ)
    [CoreMathAssumptions (builder.build p state)] :
    (builder.build p state).IsCostStationary (builder.jacobiStep state p) := by
  simpa [LocalContextBuilder.jacobiStep, LocalContextBuilder.jacobiUpdateAt] using
    FastMLFE2.Theory.Theorems.LocalContext.closedForm_isCostStationary (builder.build p state)

end LocalContextBuilder

end FastMLFE2.Theory.Theorems
