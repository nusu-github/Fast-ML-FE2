# Grid Nonempty Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a theorem-only bridge that constructively proves `Nonempty (ValidDir p)` for authored 2D grid cases where the local solver is applicable.

**Architecture:** Add a focused theorem module `GridNonempty.lean` on top of `Canonical.Grid`. Use witness-first proofs instead of cardinality detours: each theorem returns a concrete valid direction for the corresponding geometric case. Keep `Fact (Nonempty ...)` instance automation out of this cycle.

**Tech Stack:** Lean 4, mathlib4, existing `FastMLFE2.Theory.Canonical.Grid` geometry predicates and `FastMLFE2.Theory` umbrella imports.

---

## Chunk 1: Interior and Edge Witness Theorems

### Task 1: Add `GridNonempty.lean` with direct witnesses for interior and edge-noncorner cases

**Files:**
- Create: `FastMLFE2/Theory/Theorems/GridNonempty.lean`
- Reference: `FastMLFE2/Theory/Canonical/Grid.lean`
- Test: `FastMLFE2/Theory/Theorems/GridNonempty.lean`

- [ ] **Step 1: Create the theorem module skeleton**

Create `FastMLFE2/Theory/Theorems/GridNonempty.lean` with:

```lean
import FastMLFE2.Theory.Canonical.Grid

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Canonical

theorem nonempty_validDir_of_isInterior
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p) :
    Nonempty (ValidDir p) := by
  sorry

theorem nonempty_validDir_of_isTopEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hTop : IsTopEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  sorry

theorem nonempty_validDir_of_isBottomEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hBottom : IsBottomEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  sorry

theorem nonempty_validDir_of_isLeftEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hLeft : IsLeftEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  sorry

theorem nonempty_validDir_of_isRightEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hRight : IsRightEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  sorry

end FastMLFE2.Theory.Theorems
```

- [ ] **Step 2: Prove the interior case with an `up` witness**

Use:

```lean
  rcases hInterior with ⟨hUp, _, _, _⟩
  exact ⟨⟨Direction4.up, hUp⟩⟩
```

- [ ] **Step 3: Prove the top edge case with a `down` witness**

Extract the second conjunct from `IsTopEdgeNoncorner p` and use:

```lean
  exact ⟨⟨Direction4.down, hDown⟩⟩
```

- [ ] **Step 4: Prove the bottom edge case with an `up` witness**

Extract the first conjunct from `IsBottomEdgeNoncorner p` and use:

```lean
  exact ⟨⟨Direction4.up, hUp⟩⟩
```

- [ ] **Step 5: Prove the left edge case with a `right` witness**

Extract the fourth conjunct from `IsLeftEdgeNoncorner p` and use:

```lean
  exact ⟨⟨Direction4.right, hRight⟩⟩
```

- [ ] **Step 6: Prove the right edge case with a `left` witness**

Extract the third conjunct from `IsRightEdgeNoncorner p` and use:

```lean
  exact ⟨⟨Direction4.left, hLeft⟩⟩
```

- [ ] **Step 7: Run the theorem file gate**

Run: `lake env lean FastMLFE2/Theory/Theorems/GridNonempty.lean`
Expected: FAIL only because the corner theorems are not added yet, or PASS if already completed ahead of time.

- [ ] **Step 8: Commit the interior/edge theorem chunk**

```bash
git add FastMLFE2/Theory/Theorems/GridNonempty.lean
git commit -m "feat: add grid nonempty witnesses for interior and edges"
```

## Chunk 2: Corner Witness Theorems and Umbrella Import

### Task 2: Add corner witnesses and expose the module

**Files:**
- Modify: `FastMLFE2/Theory/Theorems/GridNonempty.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Theorems/Grid.lean`
- Test: `FastMLFE2/Theory/Theorems/GridNonempty.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Add the four corner theorem declarations**

Extend `GridNonempty.lean` with:

```lean
theorem nonempty_validDir_of_isTopLeftCorner
    {h w : Nat}
    [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w)
    (hCorner : IsTopLeftCorner p) :
    Nonempty (ValidDir p) := by
  sorry
```

and the analogous `TopRight`, `BottomLeft`, `BottomRight` declarations.

- [ ] **Step 2: Prove the top-left corner case with a `down` witness**

Follow the same dimensional hypotheses as `card_validDir_eq_two_of_isTopLeftCorner`.
Derive `1 < h` from `[Fact (2 ≤ h)]`, then:

```lean
  have hDown : IsValidDir p .down := by
    simpa [IsValidDir, hTop] using hHeight
  exact ⟨⟨Direction4.down, hDown⟩⟩
```

- [ ] **Step 3: Prove the top-right corner case with a `down` witness**

Use the same shape:

```lean
  have hDown : IsValidDir p .down := ...
  exact ⟨⟨Direction4.down, hDown⟩⟩
```

- [ ] **Step 4: Prove the bottom-left corner case with an `up` witness**

Derive `0 < p.1.1` from `[Fact (2 ≤ h)]` and `p.1.1 + 1 = h`, then use:

```lean
  exact ⟨⟨Direction4.up, hUp⟩⟩
```

- [ ] **Step 5: Prove the bottom-right corner case with an `up` witness**

Mirror the previous step and use the same witness shape.

- [ ] **Step 6: Import the theorem module from the theory umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Theorems.GridNonempty
```

Place it adjacent to the other grid theorem imports.

- [ ] **Step 7: Run the theorem file gate**

Run: `lake env lean FastMLFE2/Theory/Theorems/GridNonempty.lean`
Expected: PASS

- [ ] **Step 8: Run the theorem target build**

Run: `lake build FastMLFE2.Theory.Theorems.GridNonempty`
Expected: PASS

- [ ] **Step 9: Re-run the umbrella file gate**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 10: Run final library verification**

Run: `lake build FastMLFE2`
Expected: PASS

Run: `git diff --check`
Expected: no output

- [ ] **Step 11: Commit the corner/umbrella chunk**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Theorems/GridNonempty.lean
git commit -m "feat: add grid nonempty witness theorems"
```
