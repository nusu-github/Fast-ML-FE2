# Legacy Proof-Chain Cleanup Pass 2 Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Delete the remaining legacy proof-oriented module chain in one pass and reduce `FastMLFE2.Legacy` to the runtime/CLI comparison surface only.

**Architecture:** Keep `FastMLFE2.Theory` as the only proof and specification surface. Treat `FastMLFE2.Legacy` as a thin runtime umbrella over `Runtime` and `CLI`, then remove the disconnected historical proof chain modules that are no longer imported anywhere else.

**Tech Stack:** Lean 4, Lake, existing runtime/FFI executables.

---

## Chunk 1: Collapse Legacy to Runtime-Only

### Task 1: Rewrite `FastMLFE2.Legacy` as a runtime-only umbrella

**Files:**
- Modify: `FastMLFE2/Legacy.lean`
- Test: `FastMLFE2/Legacy.lean`

- [ ] **Step 1: Replace the legacy proof-chain imports with runtime-only imports**

Change `FastMLFE2/Legacy.lean` to import only:

```lean
import FastMLFE2.Runtime
import FastMLFE2.CLI
```

Keep the module doc comment but update wording if needed so it no longer suggests the old proof stack is still present.

- [ ] **Step 2: Run the legacy file gate**

Run: `lake env lean FastMLFE2/Legacy.lean`
Expected: PASS

## Chunk 2: Delete the Old Proof Chain

### Task 2: Remove the disconnected pre-refoundation proof modules

**Files:**
- Delete: `FastMLFE2/Notation.lean`
- Delete: `FastMLFE2/Compositing.lean`
- Delete: `FastMLFE2/LinearAlgebra.lean`
- Delete: `FastMLFE2/LocalCost.lean`
- Delete: `FastMLFE2/NormalEquation.lean`
- Delete: `FastMLFE2/LocalSolver.lean`
- Delete: `FastMLFE2/SummaryForm.lean`
- Delete: `FastMLFE2/LevelOperator.lean`
- Delete: `FastMLFE2/MultilevelSpec.lean`
- Delete: `FastMLFE2/ConcreteImage.lean`
- Delete: `FastMLFE2/ConcretePaper.lean`
- Test: import search only

- [ ] **Step 1: Delete the old proof-chain files**

Delete exactly these files:

- `FastMLFE2/Notation.lean`
- `FastMLFE2/Compositing.lean`
- `FastMLFE2/LinearAlgebra.lean`
- `FastMLFE2/LocalCost.lean`
- `FastMLFE2/NormalEquation.lean`
- `FastMLFE2/LocalSolver.lean`
- `FastMLFE2/SummaryForm.lean`
- `FastMLFE2/LevelOperator.lean`
- `FastMLFE2/MultilevelSpec.lean`
- `FastMLFE2/ConcreteImage.lean`
- `FastMLFE2/ConcretePaper.lean`

- [ ] **Step 2: Verify no live Lean imports still reference the deleted chain**

Run:

```bash
rg -n "import FastMLFE2\\.(Notation|Compositing|LinearAlgebra|LocalCost|NormalEquation|LocalSolver|SummaryForm|LevelOperator|MultilevelSpec|ConcreteImage|ConcretePaper)" -g '*.lean' .
```

Expected: zero matches

## Chunk 3: Fast Verification and Commit

### Task 3: Verify without repeated full rebuilds

**Files:**
- Modify: `FastMLFE2/Legacy.lean`
- Test: `FastMLFE2.lean`
- Test: `FastMLFE2/Legacy.lean`

- [ ] **Step 1: Run the theory root file gate**

Run: `lake env lean FastMLFE2.lean`
Expected: PASS

- [ ] **Step 2: Run the legacy umbrella file gate again after deletions**

Run: `lake env lean FastMLFE2/Legacy.lean`
Expected: PASS

- [ ] **Step 3: Run formatting sanity**

Run: `git diff --check`
Expected: PASS with no output

- [ ] **Step 4: Run the full build once**

Run: `lake build FastMLFE2 ffiLeanSmoke ffiCliSmoke fastmlfeCli`
Expected: PASS

- [ ] **Step 5: Commit the pass**

```bash
git add FastMLFE2/Legacy.lean
git rm FastMLFE2/Notation.lean FastMLFE2/Compositing.lean FastMLFE2/LinearAlgebra.lean FastMLFE2/LocalCost.lean FastMLFE2/NormalEquation.lean FastMLFE2/LocalSolver.lean FastMLFE2/SummaryForm.lean FastMLFE2/LevelOperator.lean FastMLFE2/MultilevelSpec.lean FastMLFE2/ConcreteImage.lean FastMLFE2/ConcretePaper.lean
git commit -m "refactor: remove legacy proof chain"
```
