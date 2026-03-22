# Legacy Umbrella Cleanup Pass 1 Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the first layer of obsolete legacy umbrella modules by deleting `FastMLFE2/Basic.lean`, `FastMLFE2/Derived.lean`, and `FastMLFE2/Spec.lean` while keeping the legacy comparison/runtime path buildable.

**Architecture:** Keep `FastMLFE2.Theory` as the only default library surface and treat `FastMLFE2.Legacy` as a compatibility umbrella. Rewire `FastMLFE2.Legacy` to import the concrete legacy modules directly, then delete the redundant umbrella modules and verify that theory and legacy entrypoints still build.

**Tech Stack:** Lean 4, Lake, existing legacy runtime/FFI targets.

---

## Chunk 1: Remove Redundant Legacy Umbrellas

### Task 1: Rewire `FastMLFE2.Legacy` away from deleted umbrella modules

**Files:**
- Modify: `FastMLFE2/Legacy.lean`
- Delete: `FastMLFE2/Basic.lean`
- Delete: `FastMLFE2/Derived.lean`
- Delete: `FastMLFE2/Spec.lean`
- Test: `FastMLFE2/Legacy.lean`

- [ ] **Step 1: Replace umbrella imports in `FastMLFE2/Legacy.lean`**

Change the imports so `FastMLFE2.Legacy` pulls in the concrete legacy modules directly:

```lean
import FastMLFE2.Notation
import FastMLFE2.Compositing
import FastMLFE2.LinearAlgebra
import FastMLFE2.LocalCost
import FastMLFE2.NormalEquation
import FastMLFE2.LocalSolver
import FastMLFE2.SummaryForm
import FastMLFE2.LevelOperator
import FastMLFE2.MultilevelSpec
import FastMLFE2.ConcreteImage
import FastMLFE2.ConcretePaper
import FastMLFE2.Runtime
import FastMLFE2.CLI
```

- [ ] **Step 2: Run the legacy umbrella file gate**

Run: `lake env lean FastMLFE2/Legacy.lean`
Expected: PASS

- [ ] **Step 3: Delete the redundant umbrella modules**

Delete:

- `FastMLFE2/Basic.lean`
- `FastMLFE2/Derived.lean`
- `FastMLFE2/Spec.lean`

- [ ] **Step 4: Verify that no live imports still reference the deleted files**

Run: `rg -n "import FastMLFE2\\.(Basic|Derived|Spec)" -g '*.lean' .`
Expected: only zero matches, or matches in historical docs if any

- [ ] **Step 5: Run the project verification set**

Run: `lake build FastMLFE2 ffiLeanSmoke ffiCliSmoke fastmlfeCli`
Expected: PASS

Run: `git diff --check`
Expected: PASS with no output

- [ ] **Step 6: Commit the cleanup**

```bash
git add FastMLFE2/Legacy.lean
git rm FastMLFE2/Basic.lean FastMLFE2/Derived.lean FastMLFE2/Spec.lean
git commit -m "refactor: remove legacy umbrella modules"
```
