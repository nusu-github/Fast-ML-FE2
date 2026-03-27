import FastMLFE2.FixedPrecision.LocalSolver

namespace FastMLFE2.FixedPrecision

abbrev FixedPixelState (cfg : FixedFormat) (κ : Type*) := κ → FixedUnknown cfg

structure FixedLocalContextBuilder (cfg : FixedFormat) (κ : Type*) (η : κ → Type*)
    [∀ p, Fintype (η p)] where
  build : (p : κ) → FixedPixelState cfg κ → FixedLocalContext cfg (η p)

namespace FixedLocalContextBuilder

variable {cfg : FixedFormat} {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

noncomputable def fixedJacobiUpdateAt
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ) : FixedUnknown cfg :=
  FixedLocalContext.fixedMeanResidualStep (builder.build p state)

noncomputable def fullyFixedJacobiUpdateAt
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ) : FixedUnknown cfg :=
  FixedLocalContext.fullyFixedMeanResidualStep (builder.build p state)

noncomputable def fixedJacobiStep
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) : FixedPixelState cfg κ :=
  fun p => fixedJacobiUpdateAt builder state p

noncomputable def fullyFixedJacobiStep
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) : FixedPixelState cfg κ :=
  fun p => fullyFixedJacobiUpdateAt builder state p

noncomputable def fixedJacobiIterate
    (builder : FixedLocalContextBuilder cfg κ η)
    (n : Nat)
    (state : FixedPixelState cfg κ) : FixedPixelState cfg κ :=
  Nat.iterate (builder.fixedJacobiStep) n state

noncomputable def fullyFixedJacobiIterate
    (builder : FixedLocalContextBuilder cfg κ η)
    (n : Nat)
    (state : FixedPixelState cfg κ) : FixedPixelState cfg κ :=
  Nat.iterate (builder.fullyFixedJacobiStep) n state

@[simp] theorem fixedJacobiUpdateAt_eq
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ) :
    builder.fixedJacobiUpdateAt state p =
      FixedLocalContext.fixedMeanResidualStep (builder.build p state) := rfl

@[simp] theorem fixedJacobiStep_apply
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ) :
    builder.fixedJacobiStep state p = builder.fixedJacobiUpdateAt state p := rfl

@[simp] theorem fullyFixedJacobiUpdateAt_eq
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ) :
    builder.fullyFixedJacobiUpdateAt state p =
      FixedLocalContext.fullyFixedMeanResidualStep (builder.build p state) := rfl

@[simp] theorem fullyFixedJacobiStep_apply
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ)
    (p : κ) :
    builder.fullyFixedJacobiStep state p = builder.fullyFixedJacobiUpdateAt state p := rfl

@[simp] theorem fixedJacobiIterate_zero
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) :
    builder.fixedJacobiIterate 0 state = state := rfl

@[simp] theorem fixedJacobiIterate_succ
    (builder : FixedLocalContextBuilder cfg κ η)
    (n : Nat)
    (state : FixedPixelState cfg κ) :
    builder.fixedJacobiIterate (n + 1) state =
      builder.fixedJacobiIterate n (builder.fixedJacobiStep state) := by
  simp [fixedJacobiIterate, Function.iterate_succ_apply]

@[simp] theorem fullyFixedJacobiIterate_zero
    (builder : FixedLocalContextBuilder cfg κ η)
    (state : FixedPixelState cfg κ) :
    builder.fullyFixedJacobiIterate 0 state = state := rfl

@[simp] theorem fullyFixedJacobiIterate_succ
    (builder : FixedLocalContextBuilder cfg κ η)
    (n : Nat)
    (state : FixedPixelState cfg κ) :
    builder.fullyFixedJacobiIterate (n + 1) state =
      builder.fullyFixedJacobiIterate n (builder.fullyFixedJacobiStep state) := by
  simp [fullyFixedJacobiIterate, Function.iterate_succ_apply]

end FixedLocalContextBuilder

end FastMLFE2.FixedPrecision
