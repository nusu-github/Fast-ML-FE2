# Jacobi Level Semantics Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a fixed-level Jacobi semantics layer that turns the proved local closed-form solver into a simultaneous one-step update on a finite pixel index set.

**Architecture:** Introduce a thin `Level/Jacobi` definition module with `PixelState`, `LocalContextBuilder`, `jacobiUpdateAt`, and `jacobiStep`, then add a theorem module that lifts existing local closed-form, normal-equation, and cost-stationary theorems pointwise. Keep the builder abstraction fully general at this stage so authored image constraints can be added later without reshaping the core semantics.

**Tech Stack:** Lean 4, mathlib4 functions on finite types, existing local-solver theorem modules in `FastMLFE2.Theory`.

---

## Chunk 1: Add the Fixed-Level Jacobi Semantics

### Task 1: Create the abstract level semantics module

**Files:**
- Create: `FastMLFE2/Theory/Level/Jacobi.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Reference: `FastMLFE2/Theory/Theorems/ClosedForm.lean`
- Test: `FastMLFE2/Theory/Level/Jacobi.lean`

- [ ] **Step 1: Add the new `Level` module skeleton**

Create `FastMLFE2/Theory/Level/Jacobi.lean` with:

```lean
import FastMLFE2.Theory.Theorems.ClosedForm

namespace FastMLFE2.Theory.Level

open FastMLFE2.Theory.Core

abbrev PixelState (κ : Type*) := κ → LocalUnknown

structure LocalContextBuilder (κ ι : Type*) [Fintype ι] where
  build : κ → PixelState κ → LocalContext ι

namespace LocalContextBuilder

variable {κ ι : Type*} [Fintype ι]

def jacobiUpdateAt
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ) : LocalUnknown :=
  FastMLFE2.Theory.Theorems.LocalContext.closedFormSolution (builder.build p state)

def jacobiStep
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ) : PixelState κ :=
  fun p => jacobiUpdateAt builder state p

end LocalContextBuilder

end FastMLFE2.Theory.Level
```

- [ ] **Step 2: Add the definitional application lemmas**

Extend `FastMLFE2/Theory/Level/Jacobi.lean` with:

```lean
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
```

- [ ] **Step 3: Import the new level module into the theory umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Level.Jacobi
```

Place it before theorem imports.

- [ ] **Step 4: Run the new level module**

Run: `lake env lean FastMLFE2/Theory/Level/Jacobi.lean`
Expected: PASS

- [ ] **Step 5: Build the module so later imports resolve cleanly**

Run: `lake build FastMLFE2.Theory.Level.Jacobi`
Expected: PASS

- [ ] **Step 6: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 7: Commit the Jacobi definition layer**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Level/Jacobi.lean
git commit -m "feat: add fixed-level jacobi semantics"
```

## Chunk 2: Lift Local Theorems Pointwise to Jacobi

### Task 2: Add the Jacobi theorem module

**Files:**
- Create: `FastMLFE2/Theory/Theorems/Jacobi.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Level/Jacobi.lean`
- Reference: `FastMLFE2/Theory/Theorems/ClosedForm.lean`
- Test: `FastMLFE2/Theory/Theorems/Jacobi.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Add the theorem module skeleton and umbrella import**

Create `FastMLFE2/Theory/Theorems/Jacobi.lean` with:

```lean
import FastMLFE2.Theory.Level.Jacobi

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level
open FastMLFE2.Theory.Assumptions

namespace LocalContextBuilder

variable {κ ι : Type*} [Fintype ι]

theorem jacobiStep_eq_closedForm
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ) :
    builder.jacobiStep state p =
      LocalContext.closedFormSolution (builder.build p state) := by
  rfl

theorem jacobiStep_solvesNormalEquation
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ)
    [CoreMathAssumptions (builder.build p state)] :
    (builder.build p state).SolvesNormalEquation (builder.jacobiStep state p) := by
  sorry

theorem jacobiStep_isCostStationary
    (builder : LocalContextBuilder κ ι)
    (state : PixelState κ)
    (p : κ)
    [CoreMathAssumptions (builder.build p state)] :
    (builder.build p state).IsCostStationary (builder.jacobiStep state p) := by
  sorry

end LocalContextBuilder

end FastMLFE2.Theory.Theorems
```

Then add:

```lean
import FastMLFE2.Theory.Theorems.Jacobi
```

to `FastMLFE2/Theory.lean`.

- [ ] **Step 2: Run the theorem file and confirm the skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/Jacobi.lean`
Expected: FAIL with unsolved goals in the two theorem bodies

- [ ] **Step 3: Prove the pointwise normal-equation theorem**

Use the existing closed-form theorem directly:

```lean
  simpa [LocalContextBuilder.jacobiStep, LocalContextBuilder.jacobiUpdateAt] using
    LocalContext.closedForm_solvesNormalEquation (builder.build p state)
```

- [ ] **Step 4: Re-run the theorem file and confirm only the stationary theorem remains**

Run: `lake env lean FastMLFE2/Theory/Theorems/Jacobi.lean`
Expected: FAIL only at `jacobiStep_isCostStationary`

- [ ] **Step 5: Prove the pointwise stationary theorem**

Use:

```lean
  simpa [LocalContextBuilder.jacobiStep, LocalContextBuilder.jacobiUpdateAt] using
    LocalContext.closedForm_isCostStationary (builder.build p state)
```

- [ ] **Step 6: Re-run the theorem module**

Run: `lake env lean FastMLFE2/Theory/Theorems/Jacobi.lean`
Expected: PASS

- [ ] **Step 7: Build the theorem module**

Run: `lake build FastMLFE2.Theory.Theorems.Jacobi`
Expected: PASS

- [ ] **Step 8: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 9: Run final library verification**

Run: `lake build FastMLFE2`
Expected: PASS

Run: `git diff --check`
Expected: no output

- [ ] **Step 10: Commit the Jacobi theorem layer**

```bash
git add FastMLFE2/Theory.lean \
  FastMLFE2/Theory/Level/Jacobi.lean \
  FastMLFE2/Theory/Theorems/Jacobi.lean
git commit -m "feat: lift local solver to jacobi level semantics"
```
