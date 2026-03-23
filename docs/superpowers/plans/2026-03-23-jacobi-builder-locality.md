# Jacobi Builder Locality Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a locality layer for abstract Jacobi builders so the theory can state when a pointwise Jacobi update depends only on a designated finite neighborhood of the old state.

**Architecture:** Introduce a thin `Level/Locality` module with neighborhood and state-agreement predicates plus the abstract `BuilderLocal` law, then add a theorem module that pushes that law through `builder.build`, `jacobiUpdateAt`, and `jacobiStep`. Keep locality extensional at this stage rather than committing to authored fieldwise builder structure.

**Tech Stack:** Lean 4, mathlib4 `Finset`, existing `Level/Jacobi` semantics in `FastMLFE2.Theory`.

---

## Chunk 1: Add Abstract Locality Predicates

### Task 1: Create the locality definition module

**Files:**
- Create: `FastMLFE2/Theory/Level/Locality.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Level/Jacobi.lean`
- Test: `FastMLFE2/Theory/Level/Locality.lean`

- [ ] **Step 1: Add the new locality module skeleton**

Create `FastMLFE2/Theory/Level/Locality.lean` with:

```lean
import FastMLFE2.Theory.Level.Jacobi

namespace FastMLFE2.Theory.Level

abbrev Neighborhood (κ : Type*) := κ → Finset κ

def StateEqOn
    {κ : Type*}
    (S : Finset κ)
    (state₁ state₂ : PixelState κ) : Prop :=
  ∀ q, q ∈ S → state₁ q = state₂ q

def BuilderLocal
    {κ ι : Type*} [Fintype ι]
    (builder : LocalContextBuilder κ ι)
    (N : Neighborhood κ) : Prop :=
  ∀ p state₁ state₂,
    StateEqOn (N p) state₁ state₂ →
      builder.build p state₁ = builder.build p state₂

end FastMLFE2.Theory.Level
```

- [ ] **Step 2: Add small helper lemmas for `StateEqOn`**

Extend `FastMLFE2/Theory/Level/Locality.lean` with:

```lean
theorem StateEqOn.refl
    {κ : Type*} (S : Finset κ) (state : PixelState κ) :
    StateEqOn S state state := by
  intro q hq
  rfl

theorem BuilderLocal.apply
    {κ ι : Type*} [Fintype ι]
    {builder : LocalContextBuilder κ ι}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.build p state₁ = builder.build p state₂ :=
  hlocal p state₁ state₂ hEq
```

- [ ] **Step 3: Import the locality definition module into the umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Level.Locality
```

Place it after `Level.Jacobi`.

- [ ] **Step 4: Run the locality module**

Run: `lake env lean FastMLFE2/Theory/Level/Locality.lean`
Expected: PASS

- [ ] **Step 5: Build the locality module**

Run: `lake build FastMLFE2.Theory.Level.Locality`
Expected: PASS

- [ ] **Step 6: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 7: Commit the locality definition layer**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Level/Locality.lean
git commit -m "feat: add jacobi builder locality predicates"
```

## Chunk 2: Prove Pointwise Locality for Jacobi Updates

### Task 2: Add the theorem layer for builder and Jacobi locality

**Files:**
- Create: `FastMLFE2/Theory/Theorems/Locality.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Level/Locality.lean`
- Reference: `FastMLFE2/Theory/Theorems/Jacobi.lean`
- Test: `FastMLFE2/Theory/Theorems/Locality.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Add the theorem module skeleton and umbrella import**

Create `FastMLFE2/Theory/Theorems/Locality.lean` with:

```lean
import FastMLFE2.Theory.Level.Locality

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Level

namespace LocalContextBuilder

variable {κ ι : Type*} [Fintype ι]

theorem build_eq_of_StateEqOn
    {builder : LocalContextBuilder κ ι}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.build p state₁ = builder.build p state₂ := by
  exact BuilderLocal.apply hlocal p hEq

theorem jacobiUpdateAt_eq_of_StateEqOn
    {builder : LocalContextBuilder κ ι}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.jacobiUpdateAt state₁ p = builder.jacobiUpdateAt state₂ p := by
  sorry

theorem jacobiStep_eq_of_StateEqOn
    {builder : LocalContextBuilder κ ι}
    {N : Neighborhood κ}
    (hlocal : BuilderLocal builder N)
    (p : κ)
    {state₁ state₂ : PixelState κ}
    (hEq : StateEqOn (N p) state₁ state₂) :
    builder.jacobiStep state₁ p = builder.jacobiStep state₂ p := by
  sorry

end LocalContextBuilder

end FastMLFE2.Theory.Theorems
```

Then add:

```lean
import FastMLFE2.Theory.Theorems.Locality
```

to `FastMLFE2/Theory.lean`.

- [ ] **Step 2: Run the theorem file and confirm the skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/Locality.lean`
Expected: FAIL with unsolved goals in the two new theorem bodies

- [ ] **Step 3: Prove locality for `jacobiUpdateAt`**

Use the builder locality theorem and rewrite through the definitions:

```lean
  simp [LocalContextBuilder.jacobiUpdateAt]
  rw [build_eq_of_StateEqOn hlocal p hEq]
```

- [ ] **Step 4: Re-run the theorem file and confirm only the `jacobiStep` theorem remains**

Run: `lake env lean FastMLFE2/Theory/Theorems/Locality.lean`
Expected: FAIL only at `jacobiStep_eq_of_StateEqOn`

- [ ] **Step 5: Prove locality for `jacobiStep`**

Use:

```lean
  simp [LocalContextBuilder.jacobiStep]
  exact jacobiUpdateAt_eq_of_StateEqOn hlocal p hEq
```

- [ ] **Step 6: Re-run the theorem module**

Run: `lake env lean FastMLFE2/Theory/Theorems/Locality.lean`
Expected: PASS

- [ ] **Step 7: Build the theorem module**

Run: `lake build FastMLFE2.Theory.Theorems.Locality`
Expected: PASS

- [ ] **Step 8: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 9: Run final library verification**

Run: `lake build FastMLFE2`
Expected: PASS

Run: `git diff --check`
Expected: no output

- [ ] **Step 10: Commit the locality theorem layer**

```bash
git add FastMLFE2/Theory.lean \
  FastMLFE2/Theory/Level/Locality.lean \
  FastMLFE2/Theory/Theorems/Locality.lean
git commit -m "feat: prove jacobi builder locality"
```
