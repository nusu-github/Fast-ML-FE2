# FastMLFE2 Theory Kernel Refoundation Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish the first theory-first kernel for FastMLFE2 by introducing pure Lean theory modules, canonical authored commitments, explicit assumption bundles, and the first invertibility and closed-form theorems for the single-pixel local equation.

**Architecture:** Build a new `FastMLFE2.Theory` tree that starts from raw local inputs `(alpha_i, I_i^c, alpha_j, F_j^c, B_j^c, epsilon_r, omega)` instead of the old pre-collapsed `totalWeight` abstraction. Keep runtime, FFI, CLI, and native code available only as legacy comparison leaves so the theory library can typecheck and evolve without OpenCV or backend scheduling choices defining correctness.

**Tech Stack:** Lean 4, mathlib4, Lake, existing FastMLFE2 local algebra files as salvage references, `main.tex`, PyMatting CPU and GPU reference sources.

---

## File Structure

### New files

- `FastMLFE2/Theory.lean`
  Theory-first umbrella import for the new formal kernel.
- `FastMLFE2/Theory/Core/LocalEquation.lean`
  Raw local context, derived neighbor weights, local cost, normal matrix, right-hand side, and core algebraic definitions.
- `FastMLFE2/Theory/Core/LocalSemantics.lean`
  Denotational predicates and solution relations for the local problem. This file must not define a fake derivative surrogate such as the old `halfGradient`.
- `FastMLFE2/Theory/Canonical/LocalCommitments.lean`
  Canonical authored commitments shared across the paper and PyMatting CPU/GPU where they agree.
- `FastMLFE2/Theory/Canonical/MultilevelSchedule.lean`
  Canonical level-count and per-level size formulas from the paper and authored implementations.
- `FastMLFE2/Theory/Assumptions/Bundles.lean`
  Explicit assumption bundles for mathematics, semantic variants, and hardware models.
- `FastMLFE2/Theory/Theorems/Invertibility.lean`
  The first well-posedness theorem family for the local system.
- `FastMLFE2/Theory/Theorems/ClosedForm.lean`
  The first algebraic equivalence theorem family for the local closed form.
- `FastMLFE2/Legacy.lean`
  Umbrella import for the old runtime-centric stack.

### Modified files

- `FastMLFE2.lean`
  Change the umbrella import from runtime-first to theory-first.
- `lakefile.lean`
  Remove native FFI from the default Lean library path and keep it only on legacy executables and comparison targets.
- `README.md`
  Update repository positioning so theory is the source of truth and runtime/native code is legacy comparison infrastructure.

### Reference-only files

These files may be copied from or mined for lemmas, but new theory files must not import them as architectural dependencies.

- `FastMLFE2/LocalCost.lean`
- `FastMLFE2/NormalEquation.lean`
- `FastMLFE2/LocalSolver.lean`
- `FastMLFE2/LinearAlgebra.lean`
- `main.tex`
- `foreground-estimation-evaluation/.venv/lib/python3.11/site-packages/pymatting/foreground/estimate_foreground_ml.py`
- `foreground-estimation-evaluation/.venv/lib/python3.11/site-packages/pymatting/foreground/estimate_foreground_ml_cupy.py`

### Deliberate non-goals for this plan

- Do not prove the derivative-from-cost theorem in this phase.
- Do not reintroduce `totalWeight > 0` as the root assumption. The new root object must retain `epsilon_r`, `omega`, and neighbor alphas so positivity can be proved from first principles.
- Do not implement backend-specific semantics, multilevel lifting theorems, or refinement IR in this phase.

## Chunk 1: Theory Root and Pure Build Path

### Task 1: Rewire the root modules around the theory kernel

**Files:**
- Create: `FastMLFE2/Theory.lean`
- Create: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Create: `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Create: `FastMLFE2/Theory/Canonical/LocalCommitments.lean`
- Create: `FastMLFE2/Theory/Canonical/MultilevelSchedule.lean`
- Create: `FastMLFE2/Theory/Assumptions/Bundles.lean`
- Create: `FastMLFE2/Theory/Theorems/Invertibility.lean`
- Create: `FastMLFE2/Theory/Theorems/ClosedForm.lean`
- Modify: `FastMLFE2.lean`
- Modify: `lakefile.lean`
- Test: `FastMLFE2.lean`

- [ ] **Step 1: Point the umbrella import at the new theory root**

```lean
-- FastMLFE2.lean
import FastMLFE2.Theory
```

- [ ] **Step 2: Run the root typecheck and confirm it fails because the new theory tree does not exist yet**

Run: `lake env lean FastMLFE2.lean`
Expected: FAIL with a missing import error for `FastMLFE2.Theory` or one of its child modules.

- [ ] **Step 3: Create minimal theory scaffolding and decouple the default library from native FFI**

```lean
-- FastMLFE2/Theory.lean
import FastMLFE2.Theory.Core.LocalEquation
import FastMLFE2.Theory.Core.LocalSemantics
import FastMLFE2.Theory.Canonical.LocalCommitments
import FastMLFE2.Theory.Canonical.MultilevelSchedule
import FastMLFE2.Theory.Assumptions.Bundles
import FastMLFE2.Theory.Theorems.Invertibility
import FastMLFE2.Theory.Theorems.ClosedForm
```

```lean
-- lakefile.lean
@[default_target] lean_lib FastMLFE2

lean_exe ffiLeanSmoke where
  root := `FFILeanSmoke
  extraDepTargets := #[`fastmlfe2ffi]
```

Use the same pattern for the existing legacy executables and native targets. Create each new theory file with a module header, namespace, and a short doc comment so the umbrella import compiles before real definitions land.

- [ ] **Step 4: Run the theory-only build**

Run: `lake env lean FastMLFE2.lean`
Expected: PASS

Run: `lake build FastMLFE2`
Expected: PASS without failing on OpenCV or native FFI compilation for the pure library target.

- [ ] **Step 5: Commit the scaffolding**

```bash
git add FastMLFE2.lean lakefile.lean FastMLFE2/Theory.lean FastMLFE2/Theory
git commit -m "refactor: scaffold theory-first module tree"
```

## Chunk 2: Raw Local Equation and Denotational Semantics

### Task 2: Define the raw local context and cost model

**Files:**
- Modify: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Modify: `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Reference: `FastMLFE2/LocalCost.lean`
- Reference: `FastMLFE2/NormalEquation.lean`
- Test: `FastMLFE2/Theory/Core/LocalEquation.lean`

- [ ] **Step 1: Add a failing consumer that uses the intended raw API**

```lean
-- FastMLFE2/Theory/Core/LocalSemantics.lean
example {ι : Type} [Fintype ι] (ctx : LocalContext ι) :
    ctx.totalWeight = ∑ j, ctx.neighborWeight j := by
  simp [LocalContext.totalWeight]
```

- [ ] **Step 2: Run the local-core typecheck and confirm it fails because the raw context API is still missing**

Run: `lake env lean FastMLFE2/Theory/Core/LocalSemantics.lean`
Expected: FAIL with unknown constant errors for `LocalContext`, `totalWeight`, or `neighborWeight`.

- [ ] **Step 3: Implement the raw local context in `LocalEquation.lean`**

```lean
structure LocalContext (ι : Type u) [Fintype ι] where
  alphaCenter : ℝ
  imageValue : ℝ
  alphaNeighbor : ι → ℝ
  fgNeighbor : ι → ℝ
  bgNeighbor : ι → ℝ
  epsilonR : ℝ
  omega : ℝ

abbrev LocalUnknown := Fin 2 → ℝ

def LocalContext.neighborWeight (ctx : LocalContext ι) (j : ι) : ℝ :=
  ctx.epsilonR + ctx.omega * |ctx.alphaCenter - ctx.alphaNeighbor j|

def LocalContext.totalWeight (ctx : LocalContext ι) : ℝ :=
  ∑ j, ctx.neighborWeight j
```

Also define:

- `localCost`
- `normalMatrix`
- `rhs`
- `compositingResidual`

Do not define a primitive `weights : ι → ℝ`. The new theory must derive weights from `epsilonR`, `omega`, and alpha differences so positivity theorems are meaningful.

- [ ] **Step 4: Run the local-equation file**

Run: `lake env lean FastMLFE2/Theory/Core/LocalEquation.lean`
Expected: PASS

- [ ] **Step 5: Implement the denotational local semantics**

```lean
def SolvesNormalEquation {ι : Type u} [Fintype ι]
    (ctx : LocalContext ι) (g : LocalUnknown) : Prop :=
  (ctx.normalMatrix).mulVec g = ctx.rhs
```

Add:

- `IsLocalSolution`
- simple definitional lemmas such as `totalWeight_eq_sum_neighborWeight`
- a module doc comment stating that derivative-based stationary theorems are intentionally deferred

Do not port or rename the old `halfGradient` definition into this layer.

- [ ] **Step 6: Re-run the core semantics file**

Run: `lake env lean FastMLFE2/Theory/Core/LocalSemantics.lean`
Expected: PASS

- [ ] **Step 7: Commit the raw local theory**

```bash
git add FastMLFE2/Theory/Core/LocalEquation.lean FastMLFE2/Theory/Core/LocalSemantics.lean
git commit -m "feat: formalize raw local equation core"
```

## Chunk 3: Canonical Commitments and Assumption Bundles

### Task 3: Encode canonical authored commitments

**Files:**
- Modify: `FastMLFE2/Theory/Canonical/LocalCommitments.lean`
- Modify: `FastMLFE2/Theory/Canonical/MultilevelSchedule.lean`
- Reference: `main.tex`
- Reference: `foreground-estimation-evaluation/.venv/lib/python3.11/site-packages/pymatting/foreground/estimate_foreground_ml.py`
- Reference: `foreground-estimation-evaluation/.venv/lib/python3.11/site-packages/pymatting/foreground/estimate_foreground_ml_cupy.py`
- Test: `FastMLFE2/Theory/Canonical/LocalCommitments.lean`

- [ ] **Step 1: Add a failing canonical-commitment check**

```lean
-- FastMLFE2/Theory/Canonical/LocalCommitments.lean
#check canonicalCommitments
```

- [ ] **Step 2: Run the canonical file and confirm it fails because the commitment layer is still empty**

Run: `lake env lean FastMLFE2/Theory/Canonical/LocalCommitments.lean`
Expected: FAIL with an unknown constant error for `canonicalCommitments`.

- [ ] **Step 3: Implement the canonical authored commitments**

```lean
inductive NeighborhoodStencil where
  | fourConnected

inductive ResizeRule where
  | nearestNeighbor

inductive ProjectionPlacement where
  | insideIteration

structure CanonicalCommitments where
  neighborhood : NeighborhoodStencil
  resize : ResizeRule
  projection : ProjectionPlacement

def canonicalCommitments : CanonicalCommitments :=
  { neighborhood := .fourConnected
  , resize := .nearestNeighbor
  , projection := .insideIteration
  }
```

Add short source notes explaining that these definitions are fixed because the paper and authored CPU/GPU implementations agree on them.

- [ ] **Step 4: Implement the canonical multilevel schedule**

```lean
def levelCount (w h : Nat) : Nat

def levelWidth (baseWidth levelCount level : Nat) : Nat

def levelHeight (baseHeight levelCount level : Nat) : Nat
```

Implement these definitions with the authored formulas from the approved spec in the same file, using the actual `Nat` and rounding helpers available in Lean and mathlib rather than leaving the schedule as prose.

- [ ] **Step 5: Verify the canonical modules**

Run: `lake env lean FastMLFE2/Theory/Canonical/LocalCommitments.lean`
Expected: PASS

Run: `lake env lean FastMLFE2/Theory/Canonical/MultilevelSchedule.lean`
Expected: PASS

- [ ] **Step 6: Commit the canonical layer**

```bash
git add FastMLFE2/Theory/Canonical/LocalCommitments.lean FastMLFE2/Theory/Canonical/MultilevelSchedule.lean
git commit -m "feat: add canonical authored commitments"
```

### Task 4: Define only the assumption bundles needed by the first theorem family

**Files:**
- Modify: `FastMLFE2/Theory/Assumptions/Bundles.lean`
- Modify: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Test: `FastMLFE2/Theory/Assumptions/Bundles.lean`

- [ ] **Step 1: Add a failing theorem-shaped use of the assumption bundles**

```lean
-- FastMLFE2/Theory/Assumptions/Bundles.lean
example {ι : Type} [Fintype ι] (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.epsilonR := by
  exact (inferInstance : CoreMathAssumptions ctx).epsilon_pos
```

- [ ] **Step 2: Run the assumption-bundle file and confirm it fails because the bundle API does not exist yet**

Run: `lake env lean FastMLFE2/Theory/Assumptions/Bundles.lean`
Expected: FAIL with unknown constant errors for `CoreMathAssumptions`.

- [ ] **Step 3: Implement the minimal assumption bundles**

```lean
class CoreMathAssumptions {ι : Type u} [Fintype ι] (ctx : LocalContext ι) : Prop where
  epsilon_pos : 0 < ctx.epsilonR
  omega_nonneg : 0 ≤ ctx.omega
  alpha_bounded : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1
  neighbor_nonempty : Nonempty ι
```

Also define small initial structures for:

- `AlphaAssumptions`
- `ChannelAssumptions`
- `VariantAssumptions`
- `InitializationAssumptions`
- `ProjectionAssumptions`
- `HardwareAssumptions`

Keep them intentionally narrow. Only add fields the first theorem family or the canonical-layer definitions actually need.

- [ ] **Step 4: Verify the assumption bundles**

Run: `lake env lean FastMLFE2/Theory/Assumptions/Bundles.lean`
Expected: PASS

- [ ] **Step 5: Commit the assumption layer**

```bash
git add FastMLFE2/Theory/Assumptions/Bundles.lean FastMLFE2/Theory/Core/LocalEquation.lean
git commit -m "feat: add theory assumption bundles"
```

## Chunk 4: First Well-Posedness and Closed-Form Theorems

### Task 5: Prove determinant positivity and invertibility from raw assumptions

**Files:**
- Modify: `FastMLFE2/Theory/Theorems/Invertibility.lean`
- Modify: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Reference: `FastMLFE2/LocalSolver.lean`
- Test: `FastMLFE2/Theory/Theorems/Invertibility.lean`

- [ ] **Step 1: Write failing theorem skeletons**

```lean
theorem totalWeight_pos_of_coreMath
    {ι : Type u} [Fintype ι]
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < ctx.totalWeight := by
  simp
```

```lean
theorem det_normalMatrix_pos
    {ι : Type u} [Fintype ι]
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 < (ctx.normalMatrix).det := by
  simp
```

- [ ] **Step 2: Run the theorem file and confirm it fails with unsolved goals**

Run: `lake env lean FastMLFE2/Theory/Theorems/Invertibility.lean`
Expected: FAIL with remaining goals for positivity or determinant algebra.

- [ ] **Step 3: Port only the needed local algebra lemmas into the new namespace**

Use `FastMLFE2/LocalSolver.lean` as a reference for determinant algebra, but rewrite the proofs against the new raw context so the result depends on `epsilonR`, `omega`, and neighbor alphas rather than on a primitive `totalWeight > 0` assumption.

- [ ] **Step 4: Prove positivity from first principles**

Prove, in order:

- each `neighborWeight` is nonnegative under `CoreMathAssumptions`
- `ctx.totalWeight` is positive because `epsilonR > 0` and `ι` is nonempty
- the determinant formula for `ctx.normalMatrix`
- determinant positivity and the corresponding nonzero corollary

Do not weaken the theorem back to "assume `0 < totalWeight`". That would recreate the gap this refoundation is supposed to close.

- [ ] **Step 5: Re-run the invertibility file**

Run: `lake env lean FastMLFE2/Theory/Theorems/Invertibility.lean`
Expected: PASS

- [ ] **Step 6: Commit the well-posedness theorems**

```bash
git add FastMLFE2/Theory/Theorems/Invertibility.lean FastMLFE2/Theory/Core/LocalEquation.lean
git commit -m "feat: prove local invertibility theorems"
```

### Task 6: Prove the analytic closed form against the abstract local solution

**Files:**
- Modify: `FastMLFE2/Theory/Theorems/ClosedForm.lean`
- Modify: `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Reference: `FastMLFE2/LocalSolver.lean`
- Test: `FastMLFE2/Theory/Theorems/ClosedForm.lean`

- [ ] **Step 1: Write failing closed-form theorem skeletons**

```lean
noncomputable def closedFormSolution {ι : Type u} [Fintype ι]
    (ctx : LocalContext ι) : LocalUnknown :=
  ![0, 0]

theorem closedForm_solves_normalEquation
    {ι : Type u} [Fintype ι]
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    SolvesNormalEquation ctx (closedFormSolution ctx) := by
  simp [closedFormSolution, SolvesNormalEquation]
```

- [ ] **Step 2: Run the closed-form file and confirm it fails with unsolved algebra**

Run: `lake env lean FastMLFE2/Theory/Theorems/ClosedForm.lean`
Expected: FAIL with remaining matrix or field goals.

- [ ] **Step 3: Implement the real analytic closed form**

Replace the placeholder with the explicit `2 x 2` inverse expansion using the determinant proved in `Invertibility.lean`.

- [ ] **Step 4: Prove the solution theorem family**

Prove:

- `closedFormSolution` solves the normal equation
- `closedFormSolution` equals the inverse-based abstract solution
- any channel-independence lemmas needed by these proofs stay stated as matrix-shape theorems, not backend claims

Keep theorems local to algebraic equivalence. Do not introduce Jacobi, multilevel, or runtime semantics here.

- [ ] **Step 5: Run the theorem verification sweep**

Run: `lake env lean FastMLFE2/Theory/Theorems/ClosedForm.lean`
Expected: PASS

Run: `lake build FastMLFE2`
Expected: PASS

- [ ] **Step 6: Commit the closed-form theorems**

```bash
git add FastMLFE2/Theory/Theorems/ClosedForm.lean FastMLFE2/Theory/Core/LocalSemantics.lean
git commit -m "feat: prove local closed-form equivalence"
```

## Chunk 5: Legacy Isolation and Repository Positioning

### Task 7: Make legacy runtime code explicit and downstream

**Files:**
- Create: `FastMLFE2/Legacy.lean`
- Modify: `README.md`
- Modify: `FastMLFE2.lean`
- Modify: `lakefile.lean`
- Test: `README.md`

- [ ] **Step 1: Confirm the README still describes the old runtime-first positioning**

Run: `rg -n "supported runtime path|proof target" README.md`
Expected: MATCH the old wording before it is rewritten.

- [ ] **Step 2: Create the legacy umbrella and update docs**

```lean
-- FastMLFE2/Legacy.lean
import FastMLFE2.Basic
import FastMLFE2.Derived
import FastMLFE2.Spec
import FastMLFE2.Runtime
import FastMLFE2.CLI
```

Update `README.md` so it says:

- `FastMLFE2.Theory` is the new source of truth
- runtime and native code are legacy comparison artifacts
- theory theorems, not smoke tests, define correctness

- [ ] **Step 3: Run the legacy compatibility build**

Run: `lake build FastMLFE2 ffiLeanSmoke ffiCliSmoke fastmlfeCli`
Expected: PASS

If legacy executables fail after the build-graph change, fix `lakefile.lean` or direct imports. Do not pull legacy runtime modules back into `FastMLFE2.lean`.

- [ ] **Step 4: Commit the isolation pass**

```bash
git add FastMLFE2/Legacy.lean README.md FastMLFE2.lean lakefile.lean
git commit -m "refactor: isolate legacy runtime path"
```

## Final Verification Checklist

- [ ] Run: `lake env lean FastMLFE2/Theory/Core/LocalEquation.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Core/LocalSemantics.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Canonical/LocalCommitments.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Canonical/MultilevelSchedule.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Assumptions/Bundles.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Theorems/Invertibility.lean`
- [ ] Run: `lake env lean FastMLFE2/Theory/Theorems/ClosedForm.lean`
- [ ] Run: `lake build FastMLFE2`
- [ ] Run: `lake build ffiLeanSmoke ffiCliSmoke fastmlfeCli`
- [ ] Run: `git diff --check`

Expected final state:

- the new theory kernel typechecks without native dependencies defining the default library path
- determinant positivity is proved from raw assumptions rather than assumed via `totalWeight > 0`
- the closed form is connected to the abstract local solution without fake derivative definitions
- legacy runtime code is still buildable but explicitly downstream of the theory architecture
