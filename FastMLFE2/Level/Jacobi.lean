import FastMLFE2.Theorems.ClosedForm

namespace FastMLFE2.Level

/-!
Abstract fixed-level Jacobi semantics above the local closed-form solver.
-/

open FastMLFE2.Core

abbrev PixelState (κ : Type*) := κ → LocalUnknown

structure LocalContextBuilder (κ : Type*) (η : κ → Type*) [∀ p, Fintype (η p)] where
  build : (p : κ) → PixelState κ → LocalContext (η p)

namespace LocalContextBuilder

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

noncomputable def jacobiUpdateAt
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ)
    (p : κ) : LocalUnknown :=
  FastMLFE2.Theorems.LocalContext.closedFormSolution (builder.build p state)

noncomputable def jacobiStep
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ) : PixelState κ :=
  fun p => jacobiUpdateAt builder state p

@[simp] theorem jacobiUpdateAt_eq
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ)
    (p : κ) :
    builder.jacobiUpdateAt state p =
      FastMLFE2.Theorems.LocalContext.closedFormSolution (builder.build p state) := rfl

@[simp] theorem jacobiStep_apply
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ)
    (p : κ) :
    builder.jacobiStep state p = builder.jacobiUpdateAt state p := rfl

end LocalContextBuilder

end FastMLFE2.Level
