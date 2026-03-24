# Local Cost to Normal Equation Bridge Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Connect `FastMLFE2.Theory.Core.LocalContext.localCost` to the existing normal-equation semantics by proving that the true one-dimensional derivatives of the local cost vanish exactly when `ctx.normalMatrix.mulVec g = ctx.rhs`.

**Architecture:** Keep the existing raw local equation and closed-form solver unchanged, then add a thin layer of cost-line definitions and a new theorem module that works with genuine univariate derivatives along the foreground and background coordinates. This avoids reintroducing a fake gradient surrogate while still giving a formal bridge from the cost function to `SolvesNormalEquation`.

**Tech Stack:** Lean 4, mathlib4 calculus lemmas (`HasDerivAt`), existing `FastMLFE2.Theory` core and theorem modules.

---

## Chunk 1: Add Cost-Line Definitions to the Core

### Task 1: Introduce reusable foreground/background perturbation lines

**Files:**
- Modify: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Modify: `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Test: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Test: `FastMLFE2/Theory/Core/LocalSemantics.lean`

- [ ] **Step 1: Add a failing consumer for perturbation lines**

Add a temporary example to `FastMLFE2/Theory/Core/LocalSemantics.lean`:

```lean
example {ι : Type} [Fintype ι] (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.foregroundLineCost g 0 = ctx.localCost g := by
  simp
```

- [ ] **Step 2: Run the semantics file and confirm it fails because the line API is missing**

Run: `lake env lean FastMLFE2/Theory/Core/LocalSemantics.lean`
Expected: FAIL with unknown constant errors for `foregroundLineCost`

- [ ] **Step 3: Add perturbation and line-cost definitions to `LocalEquation.lean`**

Add:

```lean
def perturbForeground (g : LocalUnknown) (t : ℝ) : LocalUnknown :=
  mkLocalUnknown (foreground g + t) (background g)

def perturbBackground (g : LocalUnknown) (t : ℝ) : LocalUnknown :=
  mkLocalUnknown (foreground g) (background g + t)

def foregroundLineCost (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) : ℝ :=
  ctx.localCost (perturbForeground g t)

def backgroundLineCost (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) : ℝ :=
  ctx.localCost (perturbBackground g t)
```

Also add basic simp lemmas:

- `perturbForeground_zero`
- `perturbBackground_zero`
- `foregroundLineCost_zero`
- `backgroundLineCost_zero`
- `foreground_perturbForeground`
- `background_perturbForeground`
- `foreground_perturbBackground`
- `background_perturbBackground`

- [ ] **Step 4: Re-run the local-equation file**

Run: `lake env lean FastMLFE2/Theory/Core/LocalEquation.lean`
Expected: PASS

- [ ] **Step 5: Define cost-stationarity in `LocalSemantics.lean`**

Add:

```lean
def IsCostStationary (ctx : Ctx ι) (g : Unknown) : Prop :=
  HasDerivAt (fun t : ℝ => ctx.foregroundLineCost g t) 0 0 ∧
  HasDerivAt (fun t : ℝ => ctx.backgroundLineCost g t) 0 0
```

Also add the zero-time simp lemmas:

- `isCostStationary_iff`
- `foregroundLineCost_zero`
- `backgroundLineCost_zero`

Do not define any `halfGradient`-style object here.

- [ ] **Step 6: Re-run the semantics file**

Run: `lake env lean FastMLFE2/Theory/Core/LocalSemantics.lean`
Expected: PASS

- [ ] **Step 7: Commit the core line-cost additions**

```bash
git add FastMLFE2/Theory/Core/LocalEquation.lean FastMLFE2/Theory/Core/LocalSemantics.lean
git commit -m "feat: add local cost line semantics"
```

## Chunk 2: Prove the Cost-to-Normal-Equation Bridge

### Task 2: Prove the exact derivative formulas for the two coordinate lines

**Files:**
- Create: `FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Reference: `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Test: `FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`

- [ ] **Step 1: Add the new theorem module to the theory umbrella**

Update `FastMLFE2/Theory.lean`:

```lean
import FastMLFE2.Theory.Theorems.CostToNormalEquation
```

- [ ] **Step 2: Create a failing theorem skeleton**

Create `FastMLFE2/Theory/Theorems/CostToNormalEquation.lean` with:

```lean
theorem hasDerivAt_foregroundLineCost
    {ι : Type} [Fintype ι] (ctx : LocalContext ι) (g : LocalUnknown) :
    HasDerivAt (fun t : ℝ => ctx.foregroundLineCost g t)
      (2 * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0)) 0 := by
  sorry
```

- [ ] **Step 3: Run the new theorem file and confirm it fails on the skeleton**

Run: `lake env lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
Expected: FAIL with an unsolved goal

- [ ] **Step 4: Prove the exact quadratic expansion for the foreground line**

Add a lemma of the form:

```lean
theorem foregroundLineCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    ctx.foregroundLineCost g t =
      ctx.localCost g +
      t^2 * (ctx.alphaCenter ^ 2 + ctx.totalWeight) +
      2 * t * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0)
```

The proof should use direct algebraic expansion with existing simp lemmas for:

- `compositingResidual_eq`
- `normalMatrix_mulVec_foreground`
- `rhs_foreground`

Avoid introducing any opaque gradient surrogate.

- [ ] **Step 5: Prove the exact quadratic expansion for the background line**

Add the analogous lemma:

```lean
theorem backgroundLineCost_expand
    (ctx : LocalContext ι) (g : LocalUnknown) (t : ℝ) :
    ctx.backgroundLineCost g t =
      ctx.localCost g +
      t^2 * ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) +
      2 * t * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1)
```

- [ ] **Step 6: Derive the true derivative formulas**

Use the expansion lemmas plus standard calculus lemmas to prove:

- `hasDerivAt_foregroundLineCost`
- `hasDerivAt_backgroundLineCost`

The target derivative values must be exactly:

- `2 * (ctx.normalMatrix.mulVec g 0 - ctx.rhs 0)`
- `2 * (ctx.normalMatrix.mulVec g 1 - ctx.rhs 1)`

- [ ] **Step 7: Re-run the theorem file**

Run: `lake env lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
Expected: PASS

- [ ] **Step 8: Commit the derivative bridge lemmas**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean
git commit -m "feat: prove local cost derivative bridge"
```

## Chunk 3: Connect Cost Stationarity to the Existing Solution Semantics

### Task 3: Prove that cost stationarity is equivalent to solving the normal equation

**Files:**
- Modify: `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Modify: `FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
- Modify: `FastMLFE2/Theory/Theorems/ClosedForm.lean`
- Test: `FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`

- [ ] **Step 1: Add a failing equivalence skeleton**

In `CostToNormalEquation.lean`, add:

```lean
theorem isCostStationary_iff_solvesNormalEquation
    {ι : Type} [Fintype ι] (ctx : LocalContext ι) (g : LocalUnknown) :
    ctx.IsCostStationary g ↔ ctx.SolvesNormalEquation g := by
  sorry
```

- [ ] **Step 2: Run the theorem file and confirm it fails on the new skeleton**

Run: `lake env lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
Expected: FAIL with an unsolved goal

- [ ] **Step 3: Prove the stationarity equivalence**

Use:

- `hasDerivAt_foregroundLineCost`
- `hasDerivAt_backgroundLineCost`
- uniqueness of derivatives at a point
- the fact that `2 ≠ 0` in `ℝ`

to prove:

```lean
ctx.IsCostStationary g ↔ ctx.SolvesNormalEquation g
```

- [ ] **Step 4: Add a theorem that the closed form is cost-stationary**

In `ClosedForm.lean` or the new bridge file, add:

```lean
theorem closedForm_isCostStationary
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.IsCostStationary (closedFormSolution ctx)
```

This should be proved by chaining:

- `closedForm_solvesNormalEquation`
- `isCostStationary_iff_solvesNormalEquation`

- [ ] **Step 5: Re-run the bridge file**

Run: `lake env lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
Expected: PASS

- [ ] **Step 6: Run the closed-form theorem file**

Run: `lake env lean FastMLFE2/Theory/Theorems/ClosedForm.lean`
Expected: PASS

- [ ] **Step 7: Commit the semantic bridge**

```bash
git add FastMLFE2/Theory/Core/LocalSemantics.lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean FastMLFE2/Theory/Theorems/ClosedForm.lean
git commit -m "feat: connect local cost stationarity to normal equations"
```

## Final Verification Checklist

- [ ] Run: `lake env lean FastMLFE2/Theory/Core/LocalEquation.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Core/LocalSemantics.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Theorems/ClosedForm.lean`
- [ ] Run: `lake env lean FastMLFE2.lean`
- [ ] Run: `lake build FastMLFE2`
- [ ] Run: `git diff --check`

Expected final state:

- the local cost has a genuine derivative-based stationarity notion in the theory core
- stationarity is proved equivalent to `SolvesNormalEquation`
- the existing closed-form solution is certified as cost-stationary without reintroducing a fake gradient surrogate
