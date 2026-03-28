import FastMLFE2.Approximation.BlurFusion
import FastMLFE2.Canonical.MultilevelSchedule
import FastMLFE2.Theorems.Grid.CanonicalBuilder
import FastMLFE2.Theorems.Grid.Locality

namespace FastMLFE2.Theorems

open FastMLFE2.Level
open FastMLFE2.Canonical
open FastMLFE2.Approximation

namespace Neighborhood

variable {κ : Type*} [DecidableEq κ]

/--
Pixels of the initial state that can influence `p` after `k` simultaneous local passes.

This is the recursive support growth law behind fixed-radius blur propagation:
one pass looks at `N p`, and each extra pass expands through the same neighborhood again.
-/
def propagationNeighborhood
    (N : Neighborhood κ) : Nat → Neighborhood κ
  | 0 => fun p => {p}
  | k + 1 => fun p => (N p).biUnion (propagationNeighborhood N k)

@[simp] theorem propagationNeighborhood_zero
    (N : Neighborhood κ)
    (p : κ) :
    propagationNeighborhood N 0 p = {p} := rfl

@[simp] theorem mem_propagationNeighborhood_zero
    (N : Neighborhood κ)
    (p q : κ) :
    q ∈ propagationNeighborhood N 0 p ↔ q = p := by
  simp [propagationNeighborhood]

theorem mem_propagationNeighborhood_succ
    (N : Neighborhood κ)
    (k : Nat)
    (p q : κ) :
    q ∈ propagationNeighborhood N (k + 1) p ↔
      ∃ r ∈ N p, q ∈ propagationNeighborhood N k r := by
  simp [propagationNeighborhood, Finset.mem_biUnion]

end Neighborhood

namespace LocalContextBuilder

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

theorem blurFusionUpdateAt_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    Approximation.LocalContextBuilder.blurFusionUpdateAt builder state₁ p =
      Approximation.LocalContextBuilder.blurFusionUpdateAt builder state₂ p := by
  have hbuild : builder.build p state₁ = builder.build p state₂ :=
    build_eq_of_StateEqOn hlocal p hEq
  simp only [Approximation.LocalContextBuilder.blurFusionUpdateAt_eq, hbuild]

theorem blurFusionStep_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    Approximation.LocalContextBuilder.blurFusionStep builder state₁ p =
      Approximation.LocalContextBuilder.blurFusionStep builder state₂ p := by
  simp only [Approximation.LocalContextBuilder.blurFusionStep_apply]
  exact blurFusionUpdateAt_eq_of_StateEqOn hlocal p hEq

noncomputable def jacobiIterate
    (builder : LocalContextBuilder κ η)
    (k : Nat) : PixelState κ → PixelState κ :=
  Nat.iterate (builder.jacobiStep) k

@[simp] theorem jacobiIterate_zero
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ) :
    jacobiIterate builder 0 state = state := rfl

@[simp] theorem jacobiIterate_succ
    (builder : LocalContextBuilder κ η)
    (k : Nat)
    (state : PixelState κ) :
    jacobiIterate builder (k + 1) state =
      builder.jacobiStep (jacobiIterate builder k state) := by
  simpa [jacobiIterate] using Function.iterate_succ_apply' (builder.jacobiStep) k state

@[simp] theorem blurFusionIterate_zero
    (builder : LocalContextBuilder κ η)
    (state : PixelState κ) :
    Approximation.LocalContextBuilder.blurFusionIterate builder 0 state = state := rfl

@[simp] theorem blurFusionIterate_succ
    (builder : LocalContextBuilder κ η)
    (k : Nat)
    (state : PixelState κ) :
    Approximation.LocalContextBuilder.blurFusionIterate builder (k + 1) state =
      Approximation.LocalContextBuilder.blurFusionStep builder
        (Approximation.LocalContextBuilder.blurFusionIterate builder k state) := by
  simpa [Approximation.LocalContextBuilder.blurFusionIterate] using
    Function.iterate_succ_apply'
      (Approximation.LocalContextBuilder.blurFusionStep builder) k state

theorem jacobiIterate_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    [DecidableEq κ]
    (hlocal : BuilderLocal builder N)
    (p : κ)
    (k : Nat)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (Neighborhood.propagationNeighborhood N k p) state₁ state₂) :
    jacobiIterate builder k state₁ p =
      jacobiIterate builder k state₂ p := by
  induction k generalizing p state₁ state₂ with
  | zero =>
      simpa [jacobiIterate, Neighborhood.propagationNeighborhood] using
        hEq p (by simp)
  | succ k ih =>
      rw [jacobiIterate_succ, jacobiIterate_succ]
      apply jacobiStep_eq_of_StateEqOn hlocal p
      intro q hq
      apply ih q
      intro r hr
      exact hEq r <|
        (Neighborhood.mem_propagationNeighborhood_succ (N := N) (k := k) (p := p) (q := r)).2
          ⟨q, hq, hr⟩

theorem blurFusionIterate_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    [DecidableEq κ]
    (hlocal : BuilderLocal builder N)
    (p : κ)
    (k : Nat)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (Neighborhood.propagationNeighborhood N k p) state₁ state₂) :
    Approximation.LocalContextBuilder.blurFusionIterate builder k state₁ p =
      Approximation.LocalContextBuilder.blurFusionIterate builder k state₂ p := by
  induction k generalizing p state₁ state₂ with
  | zero =>
      simpa [Approximation.LocalContextBuilder.blurFusionIterate,
        Neighborhood.propagationNeighborhood] using
        hEq p (by simp)
  | succ k ih =>
      rw [blurFusionIterate_succ, blurFusionIterate_succ]
      apply blurFusionStep_eq_of_StateEqOn hlocal p
      intro q hq
      apply ih q
      intro r hr
      exact hEq r <|
        (Neighborhood.mem_propagationNeighborhood_succ (N := N) (k := k) (p := p) (q := r)).2
          ⟨q, hq, hr⟩

theorem blurFusionX1_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    Approximation.LocalContextBuilder.blurFusionX1 builder state₁ p =
      Approximation.LocalContextBuilder.blurFusionX1 builder state₂ p := by
  simpa [Approximation.LocalContextBuilder.blurFusionX1_eq_blurFusionStep] using
    blurFusionStep_eq_of_StateEqOn hlocal p hEq

theorem blurFusionX2_eq_of_StateEqOn
    {builder : LocalContextBuilder κ η}
    {N : Neighborhood κ}
    [DecidableEq κ]
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (Neighborhood.propagationNeighborhood N 2 p) state₁ state₂) :
    Approximation.LocalContextBuilder.blurFusionX2 builder state₁ p =
      Approximation.LocalContextBuilder.blurFusionX2 builder state₂ p := by
  simpa [Approximation.LocalContextBuilder.blurFusionX2,
    Neighborhood.propagationNeighborhood] using
    blurFusionIterate_eq_of_StateEqOn hlocal p 2 hEq

end LocalContextBuilder

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [DecidableEq κ] [∀ p, Fintype (η p)]

theorem jacobiIterate_eq_of_StateEqOn
    (data : CanonicalPixelData κ η)
    (p : κ)
    (k : Nat)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn
      (Neighborhood.propagationNeighborhood data.canonicalNeighborhood k p)
      state₁ state₂) :
    LocalContextBuilder.jacobiIterate data.canonicalBuilder k state₁ p =
      LocalContextBuilder.jacobiIterate data.canonicalBuilder k state₂ p := by
  exact LocalContextBuilder.jacobiIterate_eq_of_StateEqOn
    (builder := data.canonicalBuilder)
    (N := data.canonicalNeighborhood)
    (CanonicalPixelData.canonicalBuilder_local data)
    p k hEq

theorem blurFusionIterate_eq_of_StateEqOn
    (data : CanonicalPixelData κ η)
    (p : κ)
    (k : Nat)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn
      (Neighborhood.propagationNeighborhood data.canonicalNeighborhood k p)
      state₁ state₂) :
    Approximation.LocalContextBuilder.blurFusionIterate data.canonicalBuilder k state₁ p =
      Approximation.LocalContextBuilder.blurFusionIterate data.canonicalBuilder k state₂ p := by
  exact LocalContextBuilder.blurFusionIterate_eq_of_StateEqOn
    (builder := data.canonicalBuilder)
    (N := data.canonicalNeighborhood)
    (CanonicalPixelData.canonicalBuilder_local data)
    p k hEq

end CanonicalPixelData

namespace Canonical

theorem levelCount_three_by_three_eq_four_by_four :
    FastMLFE2.Canonical.levelCount 3 3 =
      FastMLFE2.Canonical.levelCount 4 4 := by
  decide

end Canonical

end FastMLFE2.Theorems
