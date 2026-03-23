import FastMLFE2.Theory.Theorems.ClosedForm

namespace FastMLFE2.Theory.Level

/-!
Abstract fixed-level Jacobi semantics above the local closed-form solver.
-/

open FastMLFE2.Theory.Core

abbrev PixelState (κ : Type*) := κ → LocalUnknown

structure LocalContextBuilder (κ ι : Type*) [Fintype ι] where
  build : κ → PixelState κ → LocalContext ι

namespace LocalContextBuilder

variable {κ ι : Type*} [Fintype ι]

noncomputable def jacobiUpdateAt
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ) : LocalUnknown :=
  FastMLFE2.Theory.Theorems.LocalContext.closedFormSolution (builder.build p state)

noncomputable def jacobiStep
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ) : PixelState κ :=
  fun p => jacobiUpdateAt builder state p

@[simp] theorem jacobiUpdateAt_eq
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ) :
    builder.jacobiUpdateAt state p =
      FastMLFE2.Theory.Theorems.LocalContext.closedFormSolution (builder.build p state) := rfl

@[simp] theorem jacobiStep_apply
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ) :
    builder.jacobiStep state p = builder.jacobiUpdateAt state p := rfl

end LocalContextBuilder

end FastMLFE2.Theory.Level
