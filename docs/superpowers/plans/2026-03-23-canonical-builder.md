# Canonical Builder Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a concrete authored builder layer that constructs `LocalContextBuilder` and induced neighborhoods from fixed alpha/image data plus a neighbor lookup, then prove that this canonical builder satisfies the abstract Jacobi locality law.

**Architecture:** Introduce a `Canonical/Builder` module with `CanonicalPixelData`, `toLocalContext`, `canonicalBuilder`, and `canonicalNeighborhood`, then add a theorem module exposing the builder fields and proving `BuilderLocal` for the canonical builder. Keep this layer structural and definitional; do not yet add `CoreMathAssumptions` or image-grid geometry.

**Tech Stack:** Lean 4, mathlib4 `Finset.image`, existing `Level/Jacobi` and `Level/Locality` abstractions in `FastMLFE2.Theory`.

---

## Chunk 1: Add the Canonical Builder Definitions

### Task 1: Create the authored builder construction module

**Files:**
- Create: `FastMLFE2/Theory/Canonical/Builder.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Level/Locality.lean`
- Test: `FastMLFE2/Theory/Canonical/Builder.lean`

- [ ] **Step 1: Add the new canonical builder module skeleton**

Create `FastMLFE2/Theory/Canonical/Builder.lean` with:

```lean
import FastMLFE2.Theory.Level.Locality

namespace FastMLFE2.Theory.Canonical

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level

structure CanonicalPixelData (κ ι : Type*) where
  alpha : κ → ℝ
  image : κ → ℝ
  neighborPixel : κ → ι → κ
  epsilonR : ℝ
  omega : ℝ

namespace CanonicalPixelData

variable {κ ι : Type*} [Fintype ι]

def toLocalContext
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ) : LocalContext ι :=
  { alphaCenter := data.alpha p
    imageValue := data.image p
    alphaNeighbor := fun j => data.alpha (data.neighborPixel p j)
    fgNeighbor := fun j => foreground (state (data.neighborPixel p j))
    bgNeighbor := fun j => background (state (data.neighborPixel p j))
    epsilonR := data.epsilonR
    omega := data.omega }

def canonicalBuilder
    (data : CanonicalPixelData κ ι) : LocalContextBuilder κ ι where
  build := data.toLocalContext

def canonicalNeighborhood
    (data : CanonicalPixelData κ ι) : Neighborhood κ :=
  fun p => (Finset.univ : Finset ι).image (data.neighborPixel p)

end CanonicalPixelData

end FastMLFE2.Theory.Canonical
```

- [ ] **Step 2: Add definitional helper lemmas for the induced neighborhood**

Extend `FastMLFE2/Theory/Canonical/Builder.lean` with:

```lean
theorem mem_canonicalNeighborhood
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (j : ι) :
    data.neighborPixel p j ∈ data.canonicalNeighborhood p := by
  refine Finset.mem_image.mpr ?_
  exact ⟨j, Finset.mem_univ j, rfl⟩
```

Keep this theorem in the same namespace.

- [ ] **Step 3: Import the canonical builder module into the theory umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Canonical.Builder
```

Place it with the other `Canonical` imports.

- [ ] **Step 4: Run the new canonical builder module**

Run: `lake env lean FastMLFE2/Theory/Canonical/Builder.lean`
Expected: PASS

- [ ] **Step 5: Build the canonical builder module**

Run: `lake build FastMLFE2.Theory.Canonical.Builder`
Expected: PASS

- [ ] **Step 6: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 7: Commit the canonical builder definition layer**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Canonical/Builder.lean
git commit -m "feat: add canonical jacobi builder"
```

## Chunk 2: Prove Field Correctness and Builder Locality

### Task 2: Add theorem support for the canonical builder

**Files:**
- Create: `FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Canonical/Builder.lean`
- Reference: `FastMLFE2/Theory/Theorems/Locality.lean`
- Test: `FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Add the theorem module skeleton and umbrella import**

Create `FastMLFE2/Theory/Theorems/CanonicalBuilder.lean` with:

```lean
import FastMLFE2.Theory.Canonical.Builder

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Level
open FastMLFE2.Theory.Canonical

namespace CanonicalPixelData

variable {κ ι : Type*} [Fintype ι]

@[simp] theorem canonicalBuilder_alphaCenter
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).alphaCenter = data.alpha p := by
  rfl

@[simp] theorem canonicalBuilder_imageValue
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).imageValue = data.image p := by
  rfl

@[simp] theorem canonicalBuilder_alphaNeighbor
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ)
    (j : ι) :
    (data.canonicalBuilder.build p state).alphaNeighbor j =
      data.alpha (data.neighborPixel p j) := by
  rfl

@[simp] theorem canonicalBuilder_fgNeighbor
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ)
    (j : ι) :
    (data.canonicalBuilder.build p state).fgNeighbor j =
      foreground (state (data.neighborPixel p j)) := by
  rfl

@[simp] theorem canonicalBuilder_bgNeighbor
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ)
    (j : ι) :
    (data.canonicalBuilder.build p state).bgNeighbor j =
      background (state (data.neighborPixel p j)) := by
  rfl

@[simp] theorem canonicalBuilder_epsilonR
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).epsilonR = data.epsilonR := by
  rfl

@[simp] theorem canonicalBuilder_omega
    (data : CanonicalPixelData κ ι)
    (p : κ)
    (state : PixelState κ) :
    (data.canonicalBuilder.build p state).omega = data.omega := by
  rfl

theorem canonicalBuilder_local
    (data : CanonicalPixelData κ ι) :
    BuilderLocal data.canonicalBuilder data.canonicalNeighborhood := by
  sorry

end CanonicalPixelData

end FastMLFE2.Theory.Theorems
```

Then add:

```lean
import FastMLFE2.Theory.Theorems.CanonicalBuilder
```

to `FastMLFE2/Theory.lean`.

- [ ] **Step 2: Run the theorem file and confirm the locality theorem fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`
Expected: FAIL only at `canonicalBuilder_local`

- [ ] **Step 3: Prove `canonicalBuilder_local`**

Use extensionality on the built `LocalContext` and the helper membership theorem:

```lean
  intro p state₁ state₂ hEq
  ext j <;> simp [CanonicalPixelData.canonicalBuilder, CanonicalPixelData.toLocalContext]
```

For the `fgNeighbor` and `bgNeighbor` fields, use:

```lean
  have hmem : data.neighborPixel p j ∈ data.canonicalNeighborhood p :=
    data.mem_canonicalNeighborhood p j
  exact congrArg foreground (hEq _ hmem)
```

and similarly for `background`.

- [ ] **Step 4: Re-run the theorem module**

Run: `lake env lean FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`
Expected: PASS

- [ ] **Step 5: Build the theorem module**

Run: `lake build FastMLFE2.Theory.Theorems.CanonicalBuilder`
Expected: PASS

- [ ] **Step 6: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 7: Run final library verification**

Run: `lake build FastMLFE2`
Expected: PASS

Run: `git diff --check`
Expected: no output

- [ ] **Step 8: Commit the canonical builder theorem layer**

```bash
git add FastMLFE2/Theory.lean \
  FastMLFE2/Theory/Canonical/Builder.lean \
  FastMLFE2/Theory/Theorems/CanonicalBuilder.lean
git commit -m "feat: prove canonical builder locality"
```
