import FastMLFE2.Theory.Level.Locality

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Level

namespace LocalContextBuilder

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

theorem build_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.build p state₁ = builder.build p state₂ := by
  exact BuilderLocal.apply hlocal p hEq

theorem jacobiUpdateAt_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.jacobiUpdateAt state₁ p = builder.jacobiUpdateAt state₂ p := by
  have hbuild : builder.build p state₁ = builder.build p state₂ :=
    build_eq_of_StateEqOn hlocal p hEq
  simp only [LocalContextBuilder.jacobiUpdateAt_eq, hbuild]

theorem jacobiStep_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.jacobiStep state₁ p = builder.jacobiStep state₂ p := by
  simp only [LocalContextBuilder.jacobiStep_apply]
  exact
    jacobiUpdateAt_eq_of_StateEqOn hlocal p hEq

end LocalContextBuilder

end FastMLFE2.Theory.Theorems
