# H11a Compositing Error Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a one-channel compositing semantics layer and prove the H11a recomposition error bound for foreground/background estimation.

**Architecture:** Introduce a small `Theory/Compositing` layer for the scalar compositing definition, then add a theorem module that proves an unconditional absolute-value error bound and an authored `0 ≤ α ≤ 1` corollary. Keep the new layer separate from the local solver kernel so compositing-quality semantics remains downstream of the estimation theory.

**Tech Stack:** Lean 4, mathlib4 real-number inequalities, existing `FastMLFE2.Theory` umbrella.

---

## Chunk 1: Add One-Channel Compositing Semantics

### Task 1: Create the compositing module and expose it from the theory umbrella

**Files:**
- Create: `FastMLFE2/Theory/Compositing/OneChannel.lean`
- Modify: `FastMLFE2/Theory.lean`
- Test: `FastMLFE2/Theory/Compositing/OneChannel.lean`

- [ ] **Step 1: Add the new compositing directory and module skeleton**

Create `FastMLFE2/Theory/Compositing/OneChannel.lean` with:

```lean
import Mathlib

namespace FastMLFE2.Theory.Compositing

/-- One-channel alpha compositing over `ℝ`. -/
def compose (alpha foreground background : ℝ) : ℝ :=
  alpha * foreground + (1 - alpha) * background

end FastMLFE2.Theory.Compositing
```

- [ ] **Step 2: Add basic simplification lemmas for the new semantics**

Extend `FastMLFE2/Theory/Compositing/OneChannel.lean` with:

```lean
@[simp] theorem compose_zero_alpha (foreground background : ℝ) :
    compose 0 foreground background = background := by
  simp [compose]

@[simp] theorem compose_one_alpha (foreground background : ℝ) :
    compose 1 foreground background = foreground := by
  simp [compose]

theorem compose_sub_compose
    (alpha foreground background foreground' background' : ℝ) :
    compose alpha foreground background - compose alpha foreground' background' =
      alpha * (foreground - foreground') + (1 - alpha) * (background - background') := by
  simp [compose]
  ring
```

- [ ] **Step 3: Add the new theorem import to the umbrella later by first reserving the slot**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Compositing.OneChannel
```

Place it before theorem imports.

- [ ] **Step 4: Run the new compositing module**

Run: `lake env lean FastMLFE2/Theory/Compositing/OneChannel.lean`
Expected: PASS

- [ ] **Step 5: Run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 6: Commit the compositing semantics layer**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Compositing/OneChannel.lean
git commit -m "feat: add one-channel compositing semantics"
```

## Chunk 2: Prove H11a Compositing Error Bounds

### Task 2: Add the theorem module for unconditional and authored recomposition error bounds

**Files:**
- Create: `FastMLFE2/Theory/Theorems/CompositingError.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Compositing/OneChannel.lean`
- Test: `FastMLFE2/Theory/Theorems/CompositingError.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Add the theorem module skeleton and umbrella import**

Create `FastMLFE2/Theory/Theorems/CompositingError.lean` with:

```lean
import FastMLFE2.Theory.Compositing.OneChannel

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Compositing

theorem abs_compose_sub_compose_le
    (alpha foreground background foreground' background' : ℝ) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      |alpha| * |foreground - foreground'| +
        |1 - alpha| * |background - background'| := by
  sorry

theorem abs_compose_sub_compose_le_authored
    {alpha foreground background foreground' background' : ℝ}
    (hα : 0 ≤ alpha)
    (hα' : alpha ≤ 1) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      alpha * |foreground - foreground'| +
        (1 - alpha) * |background - background'| := by
  sorry

end FastMLFE2.Theory.Theorems
```

Then add:

```lean
import FastMLFE2.Theory.Theorems.CompositingError
```

to `FastMLFE2/Theory.lean`.

- [ ] **Step 2: Run the theorem file and confirm the skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/CompositingError.lean`
Expected: FAIL with unsolved goals in the two new theorems

- [ ] **Step 3: Prove the unconditional absolute-value bound**

Use the compositing difference lemma and the triangle inequality:

```lean
  rw [compose_sub_compose]
  calc
    |alpha * (foreground - foreground') + (1 - alpha) * (background - background')|
        ≤ |alpha * (foreground - foreground')| + |(1 - alpha) * (background - background')| := by
          simpa using abs_add (alpha * (foreground - foreground')) ((1 - alpha) * (background - background'))
    _ = |alpha| * |foreground - foreground'| + |1 - alpha| * |background - background'| := by
          rw [abs_mul, abs_mul]
```

- [ ] **Step 4: Re-run the theorem file and confirm only the authored corollary remains**

Run: `lake env lean FastMLFE2/Theory/Theorems/CompositingError.lean`
Expected: FAIL only at `abs_compose_sub_compose_le_authored`

- [ ] **Step 5: Prove the authored corollary under `0 ≤ α ≤ 1`**

Use:

```lean
have hbase := abs_compose_sub_compose_le alpha foreground background foreground' background'
have habsα : |alpha| = alpha := abs_of_nonneg hα
have habs1 : |1 - alpha| = 1 - alpha := abs_of_nonneg (sub_nonneg.mpr hα')
```

then rewrite `hbase` with `habsα` and `habs1`.

- [ ] **Step 6: Add a compact summary corollary if it clarifies later use**

Only if it materially helps future proofs, add:

```lean
theorem compose_error_is_weighted_sum
    {alpha foreground background foreground' background' : ℝ}
    (hα : 0 ≤ alpha)
    (hα' : alpha ≤ 1) :
    |compose alpha foreground background - compose alpha foreground' background'| ≤
      alpha * |foreground - foreground'| + (1 - alpha) * |background - background'| :=
  abs_compose_sub_compose_le_authored hα hα'
```

If this would just duplicate the previous theorem, skip it.

- [ ] **Step 7: Re-run the theorem module**

Run: `lake env lean FastMLFE2/Theory/Theorems/CompositingError.lean`
Expected: PASS

- [ ] **Step 8: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 9: Run the library build and whitespace check**

Run: `lake build FastMLFE2`
Expected: PASS

Run: `git diff --check`
Expected: no output

- [ ] **Step 10: Commit the H11a theorem layer**

```bash
git add FastMLFE2/Theory.lean \
  FastMLFE2/Theory/Compositing/OneChannel.lean \
  FastMLFE2/Theory/Theorems/CompositingError.lean
git commit -m "feat: prove h11a compositing error bounds"
```
