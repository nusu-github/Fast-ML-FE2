import FastMLFE2.Level.Locality

namespace FastMLFE2.Theorems

open FastMLFE2.Level

namespace LocalContextBuilder

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

theorem build_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.build p state₁ = builder.build p state₂ :=
  BuilderLocal.apply hlocal p hEq

theorem jacobiUpdateAt_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.jacobiUpdateAt state₁ p = builder.jacobiUpdateAt state₂ p := by
  simp only [LocalContextBuilder.jacobiUpdateAt_eq, build_eq_of_StateEqOn hlocal p hEq]

theorem jacobiStep_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.jacobiStep state₁ p = builder.jacobiStep state₂ p := by
  simp only [LocalContextBuilder.jacobiStep_apply]
  exact jacobiUpdateAt_eq_of_StateEqOn hlocal p hEq

theorem alphaCenter_le_tau_iff_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂)
    (τ : ℝ) :
    (builder.build p state₁).alphaCenter ≤ τ ↔
      (builder.build p state₂).alphaCenter ≤ τ := by
  rw [build_eq_of_StateEqOn hlocal p hEq]

theorem one_minus_alphaCenter_le_tau_iff_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂)
    (τ : ℝ) :
    1 - (builder.build p state₁).alphaCenter ≤ τ ↔
      1 - (builder.build p state₂).alphaCenter ≤ τ := by
  rw [build_eq_of_StateEqOn hlocal p hEq]

end LocalContextBuilder

end FastMLFE2.Theorems
