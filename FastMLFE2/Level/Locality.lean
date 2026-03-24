import FastMLFE2.Level.Jacobi

namespace FastMLFE2.Level

/-!
Abstract locality predicates for fixed-level Jacobi builders.
-/

abbrev Neighborhood (κ : Type*) := κ → Finset κ

def StateEqOn
    {κ : Type*}
    (S : Finset κ)
    (state₁ state₂ : PixelState κ) : Prop :=
  ∀ q, q ∈ S → state₁ q = state₂ q

def BuilderLocal
    {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder κ η)
    (N : Neighborhood κ) : Prop :=
  ∀ p state₁ state₂,
    StateEqOn (N p) state₁ state₂ →
      builder.build p state₁ = builder.build p state₂

theorem StateEqOn.refl
    {κ : Type*}
    (S : Finset κ)
    (state : PixelState κ) :
    StateEqOn S state state := by
  intro q hq
  rfl

theorem BuilderLocal.apply
    {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.build p state₁ = builder.build p state₂ :=
  hlocal p state₁ state₂ hEq

end FastMLFE2.Level
