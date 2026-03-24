# Grid Assumptions Bridge Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a bridge from `GridPixelData` to per-pixel `CoreMathAssumptions`, so the existing local theorem kernel can be reused on faithful 2D grid contexts.

**Architecture:** Introduce a small authored-data assumption bundle in `Assumptions/Grid`, then add a theorem/instance module in `Theorems/GridAssumptions` that turns `GridMathAssumptions` plus `Fact (Nonempty (ValidDir p))` into `CoreMathAssumptions` for the canonical builder context at pixel `p`. Keep `neighborNonempty` external to the bundle and do not yet add grid-specific Jacobi wrappers.

**Tech Stack:** Lean 4, mathlib4 typeclasses, existing `Canonical.Grid`, `Canonical.Builder`, and `CoreMathAssumptions`-based local theorem modules in `FastMLFE2.Theory`.

---

## Chunk 1: Add the Grid Authored Assumption Bundle

### Task 1: Define `GridMathAssumptions`

**Files:**
- Create: `FastMLFE2/Theory/Assumptions/Grid.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Canonical/Grid.lean`
- Reference: `FastMLFE2/Theory/Assumptions/Bundles.lean`
- Test: `FastMLFE2/Theory/Assumptions/Grid.lean`

- [ ] **Step 1: Create the new grid assumption module**

Create `FastMLFE2/Theory/Assumptions/Grid.lean` with:

```lean
import FastMLFE2.Theory.Assumptions.Bundles
import FastMLFE2.Theory.Canonical.Grid

namespace FastMLFE2.Theory.Assumptions

open FastMLFE2.Theory.Canonical

class GridMathAssumptions {h w : Nat} (data : GridPixelData h w) : Prop where
  epsilonPos : 0 < data.epsilonR
  omegaNonneg : 0 ≤ data.omega
  alphaBounded : ∀ p, 0 ≤ data.alpha p ∧ data.alpha p ≤ 1

end FastMLFE2.Theory.Assumptions
```

- [ ] **Step 2: Keep the bundle intentionally minimal**

Do not add:

- `neighborNonempty`
- neighbor alpha interval assumptions
- any geometry theorem as a field

This bundle should describe only the authored data facts that are globally true for `data`.

- [ ] **Step 3: Import the module into the theory umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Assumptions.Grid
```

Place it adjacent to the other assumption imports.

- [ ] **Step 4: Run the file gate**

Run: `lake env lean FastMLFE2/Theory/Assumptions/Grid.lean`
Expected: PASS

- [ ] **Step 5: Build the assumption module**

Run: `lake build FastMLFE2.Theory.Assumptions.Grid`
Expected: PASS

- [ ] **Step 6: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 7: Commit the new assumption bundle**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Assumptions/Grid.lean
git commit -m "feat: add grid assumption bundle"
```

## Chunk 2: Bridge Grid Assumptions to `CoreMathAssumptions`

### Task 2: Add the per-pixel theorem/instance bridge

**Files:**
- Create: `FastMLFE2/Theory/Theorems/GridAssumptions.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Assumptions/Grid.lean`
- Reference: `FastMLFE2/Theory/Canonical/Grid.lean`
- Reference: `FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`
- Test: `FastMLFE2/Theory/Theorems/GridAssumptions.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Create the theorem module skeleton**

Create `FastMLFE2/Theory/Theorems/GridAssumptions.lean` with:

```lean
import FastMLFE2.Theory.Assumptions.Grid
import FastMLFE2.Theory.Theorems.CanonicalBuilder

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions
open FastMLFE2.Theory.Canonical

namespace GridPixelData

variable {h w : Nat}
variable (data : GridPixelData h w)
variable (state : FastMLFE2.Theory.Level.PixelState (Pixel h w))
variable (p : Pixel h w)

instance coreMathAssumptions_of_gridMathAssumptions
    [GridMathAssumptions data]
    [Fact (Nonempty (ValidDir p))] :
    CoreMathAssumptions ((data.toCanonicalPixelData).canonicalBuilder.build p state) := by
  sorry

end GridPixelData

end FastMLFE2.Theory.Theorems
```

- [ ] **Step 2: Run the theorem file and verify it fails only at the bridge body**

Run: `lake env lean FastMLFE2/Theory/Theorems/GridAssumptions.lean`
Expected: FAIL with one unsolved theorem body

- [ ] **Step 3: Prove the `epsilonPos` and `omegaNonneg` fields**

Use the canonical builder field theorems so the proof is definition-light:

- `canonicalBuilder_epsilonR`
- `canonicalBuilder_omega`

These should let the corresponding fields follow by `simpa`.

- [ ] **Step 4: Prove the `alphaCenterBounded` field**

Use:

- `canonicalBuilder_alphaCenter`
- `GridMathAssumptions.alphaBounded data p`

Again, keep the proof as a short `simpa`.

- [ ] **Step 5: Prove the `neighborNonempty` field**

Use the explicit local witness:

```lean
  exact Fact.out
```

The important point is that this field comes from `Fact (Nonempty (ValidDir p))`, not from
`GridMathAssumptions`.

- [ ] **Step 6: Import the theorem module into the theory umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Theorems.GridAssumptions
```

Place it with the other theorem imports.

- [ ] **Step 7: Re-run the theorem file**

Run: `lake env lean FastMLFE2/Theory/Theorems/GridAssumptions.lean`
Expected: PASS

- [ ] **Step 8: Build the theorem module**

Run: `lake build FastMLFE2.Theory.Theorems.GridAssumptions`
Expected: PASS

- [ ] **Step 9: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 10: Run final library verification**

Run: `lake build FastMLFE2`
Expected: PASS

Run: `git diff --check`
Expected: no output

- [ ] **Step 11: Commit the bridge layer**

```bash
git add FastMLFE2/Theory.lean \
  FastMLFE2/Theory/Assumptions/Grid.lean \
  FastMLFE2/Theory/Theorems/GridAssumptions.lean
git commit -m "feat: bridge grid assumptions to local solver"
```
