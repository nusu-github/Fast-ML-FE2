# Review Gaps Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the six formal gaps identified by `lean4:review`, centred on the missing global-minimality theorem, a documentation error, and several missing bridge lemmas.

**Architecture:** Each gap becomes one isolated Lean file edit (or new file) plus an `FastMLFE2.lean` import where needed. All proofs build on already-compiled lemmas; no new dependencies are required. The hardest item (global minimality) requires two intermediate lemmas that are proved first inside the same file.

**Tech Stack:** Lean 4 v4.28.0, Mathlib v4.28.0. Verification ladder: `lean_diagnostic_messages` per edit → `lake env lean <file>` per file → `lake build` at the end of each task.

---

## Files Created / Modified

| File | Action | Purpose |
|------|--------|---------|
| `docs/architecture.md` | Modify line 243 | Fix `rawStepGain < 1` → `rawStepGain ≥ 1` |
| `FastMLFE2/Theorems/Grid/ChannelReuse.lean` | Modify (append) | Add `normalMatrixInv_eq_of_sameWeightData` |
| `FastMLFE2/Theorems/Approximation/ClosedFormMeanResidual.lean` | Modify (append) | Add `compositingResidual_closedFormSolution_eq` |
| `FastMLFE2/Theorems/Solvability/GlobalMinimality.lean` | **Create** | `localCost_closedFormSolution_le` — global optimality |
| `FastMLFE2.lean` | Modify (append) | Import new GlobalMinimality file |
| `FastMLFE2/Theorems/Iteration/JacobiTermination.lean` | **Create** | Bridge: Jacobi early-termination from ContractionBounds |
| `FastMLFE2.lean` | Modify (append) | Import new JacobiTermination file |

---

## Task 1 — Fix architecture.md documentation error

**Files:**
- Modify: `docs/architecture.md:243`

- [ ] **Step 1: Confirm the mismatch**

Run:
```bash
grep -n "rawStepGain" docs/architecture.md
```
Expected: line containing `rawStepGain < 1`.

- [ ] **Step 2: Apply fix**

In `docs/architecture.md`, replace the affected bullet (currently around line 243):

Old text (exact match):
```
- **ClampPlacement** — `rawStepGain < 1`; inside-clamped and end-clamped iterates have
```

New text:
```
- **ClampPlacement** — `rawStepGain ≥ 1` (unclamped step can overshoot); inside-clamped and end-clamped iterates have
```

- [ ] **Step 3: Verify grep is gone**

```bash
grep -n "rawStepGain < 1" docs/architecture.md
```
Expected: no output.

- [ ] **Step 4: Commit**

```bash
git add docs/architecture.md
git commit -m "docs: fix rawStepGain description — ≥ 1 not < 1"
```

---

## Task 2 — Add `normalMatrixInv_eq_of_sameWeightData` to ChannelReuse

The paper states: "the matrix $(U_i U_i^T + R^T V_i R)^{-1}$ is independent of $c$, which means it only has to be computed once per pixel." The formal counterpart is that the *inverse* is equal across same-weight contexts. `normalMatrix_eq_of_sameWeightData` already exists; this adds the corollary.

**Files:**
- Modify: `FastMLFE2/Theorems/Grid/ChannelReuse.lean` (append before final `end` blocks)

- [ ] **Step 1: State the theorem with sorry**

Append the following before the closing `end LocalContext` in `FastMLFE2/Theorems/Grid/ChannelReuse.lean`:

```lean
/-- The normal-matrix inverse is channel-independent: only weight data (α, ε_r, ω)
determines the inverse; image values and neighbor colors do not. -/
theorem normalMatrixInv_eq_of_sameWeightData
    {ctx₁ ctx₂ : LocalContext ι} (h : SameWeightData ctx₁ ctx₂) :
    ctx₁.normalMatrix⁻¹ = ctx₂.normalMatrix⁻¹ := by
  sorry
```

- [ ] **Step 2: Verify type-checks**

```bash
lake env lean FastMLFE2/Theorems/Grid/ChannelReuse.lean
```
Expected: no errors (sorry is accepted by the type checker).

- [ ] **Step 3: Implement the proof**

Replace the `sorry` with:
```lean
  congr 1
  exact normalMatrix_eq_of_sameWeightData h
```

- [ ] **Step 4: Verify compiles cleanly**

```bash
lake env lean FastMLFE2/Theorems/Grid/ChannelReuse.lean
```
Expected: no errors, no warnings about sorry.

- [ ] **Step 5: Commit**

```bash
git add FastMLFE2/Theorems/Grid/ChannelReuse.lean
git commit -m "feat: add normalMatrixInv_eq_of_sameWeightData to ChannelReuse"
```

---

## Task 3 — Add compositing residual equation at solution

The compositing residual `α F* + (1−α) B* − I` at the closed-form solution is non-zero in general (the solver does not enforce the compositing equation exactly), but it equals a scaled mean-residual. Making this explicit is the quality-guarantee formula.

**Files:**
- Modify: `FastMLFE2/Theorems/Approximation/ClosedFormMeanResidual.lean` (append before final `end` blocks)

- [ ] **Step 1: State with sorry**

Append before the closing `end LocalContext` in `ClosedFormMeanResidual.lean`:

```lean
/-- The compositing residual at the closed-form solution equals
`-(totalWeight / weightedMeanDenom) * meanResidual`.
As `totalWeight → ∞` (many neighbours) or `meanResidual → 0` (inputs already consistent)
the residual vanishes. -/
theorem compositingResidual_closedFormSolution_eq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    ctx.compositingResidual (closedFormSolution ctx) =
      -(ctx.totalWeight / ctx.weightedMeanDenom) * ctx.meanResidual := by
  sorry
```

- [ ] **Step 2: Verify type-checks**

```bash
lake env lean FastMLFE2/Theorems/Approximation/ClosedFormMeanResidual.lean
```
Expected: no errors.

- [ ] **Step 3: Implement the proof**

The derivation uses `foreground_correction_uses_meanResidual` and `background_correction_uses_meanResidual` already in this file:

Replace `sorry` with:

```lean
  have hden : ctx.weightedMeanDenom ≠ 0 := (weightedMeanDenom_pos ctx).ne'
  simp only [LocalContext.compositingResidual_eq,
    foreground_correction_uses_meanResidual ctx,
    background_correction_uses_meanResidual ctx]
  have : ctx.weightedMeanDenom = ctx.totalWeight + ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 := by
    simp [LocalContext.weightedMeanDenom]; ring
  field_simp [hden]
  ring
```

- [ ] **Step 4: Verify compiles cleanly**

```bash
lake env lean FastMLFE2/Theorems/Approximation/ClosedFormMeanResidual.lean
```
Expected: no errors.

- [ ] **Step 5: Commit**

```bash
git add FastMLFE2/Theorems/Approximation/ClosedFormMeanResidual.lean
git commit -m "feat: add compositingResidual_closedFormSolution_eq"
```

---

## Task 4 — Prove global minimality of closedFormSolution (main gap)

This is the central missing theorem. The cost function is a convex quadratic, so the unique stationary point is a global minimum. The proof proceeds in three lemmas:

1. **Quadratic form non-negativity**: `d^T M d ≥ 0` for the positive-definite `normalMatrix`.
2. **Cost difference identity**: `localCost g − localCost g* = (g − g*)^T M (g − g*)`.
3. **Global minimality**: combine 1 + 2.

**Files:**
- **Create:** `FastMLFE2/Theorems/Solvability/GlobalMinimality.lean`
- Modify: `FastMLFE2.lean` (add import)

- [ ] **Step 1: Create the file with all sorry stubs**

Create `FastMLFE2/Theorems/Solvability/GlobalMinimality.lean`:

```lean
import FastMLFE2.Theorems.Solvability.ClosedForm
import FastMLFE2.Theorems.Solvability.Invertibility

namespace FastMLFE2.Theorems

/-!
Global minimality of the closed-form solution.

The local cost function is a convex quadratic:
  localCost g = gᵀ M g − 2 rhsᵀ g + C
where M = normalMatrix is positive definite under `CoreMathAssumptions`.
Therefore the unique stationary point `closedFormSolution` is the global minimizer.
-/

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- The 2×2 quadratic form `d^T M d` is non-negative when M = normalMatrix is
positive definite. Proof: complete the square using `det M > 0` and `diag > 0`. -/
private theorem normalMatrix_quadratic_form_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (d : LocalUnknown) :
    0 ≤ (ctx.alphaCenter ^ 2 + ctx.totalWeight) * foreground d ^ 2 +
      2 * (ctx.alphaCenter * (1 - ctx.alphaCenter)) * (foreground d * background d) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * background d ^ 2 := by
  sorry

/-- Cost difference identity:
  `localCost g − localCost g* = (g − g*)^T M (g − g*)`. -/
private theorem localCost_sub_closedForm_eq
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (g : LocalUnknown) :
    ctx.localCost g - ctx.localCost (closedFormSolution ctx) =
      (ctx.alphaCenter ^ 2 + ctx.totalWeight) *
          (foreground g - foreground (closedFormSolution ctx)) ^ 2 +
        2 * (ctx.alphaCenter * (1 - ctx.alphaCenter)) *
          ((foreground g - foreground (closedFormSolution ctx)) *
            (background g - background (closedFormSolution ctx))) +
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) *
          (background g - background (closedFormSolution ctx)) ^ 2 := by
  sorry

/-- **Global minimality**: the closed-form solution minimizes the local cost function
over all `LocalUnknown` vectors. -/
theorem localCost_closedFormSolution_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] (g : LocalUnknown) :
    ctx.localCost (closedFormSolution ctx) ≤ ctx.localCost g := by
  sorry

end LocalContext

end FastMLFE2.Theorems
```

- [ ] **Step 2: Verify sorry file type-checks**

```bash
lake env lean FastMLFE2/Theorems/Solvability/GlobalMinimality.lean
```
Expected: no errors (sorry accepted).

- [ ] **Step 3: Prove `normalMatrix_quadratic_form_nonneg`**

Replace its `sorry` with:

```lean
  set a := ctx.alphaCenter ^ 2 + ctx.totalWeight
  set b := (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight
  set c := ctx.alphaCenter * (1 - ctx.alphaCenter)
  set x := foreground d
  set y := background d
  have ha : 0 < a := by
    simpa [a, jacobiDiagForeground] using jacobiDiagForeground_pos ctx
  have hdet : 0 < a * b - c ^ 2 := by
    have := normalMatrix_det_pos ctx
    simp only [normalMatrix_det, LocalContext.normalMatrix, Matrix.det_fin_two] at this
    simp only [a, b, c]; linarith
  -- Complete the square: a*(a*x^2 + 2c*x*y + b*y^2) = (a*x + c*y)^2 + (ab - c^2)*y^2
  nlinarith [sq_nonneg (a * x + c * y), sq_nonneg y,
    show a * (a * x ^ 2 + 2 * c * (x * y) + b * y ^ 2) =
        (a * x + c * y) ^ 2 + (a * b - c ^ 2) * y ^ 2 by ring]
```

- [ ] **Step 4: Verify step 3 compiles**

```bash
lake env lean FastMLFE2/Theorems/Solvability/GlobalMinimality.lean
```
Expected: no errors on `normalMatrix_quadratic_form_nonneg`.

- [ ] **Step 5: Prove `localCost_sub_closedForm_eq`**

Replace its `sorry` with:

```lean
  set g' := closedFormSolution ctx
  have hsolve : ctx.normalMatrix.mulVec g' = ctx.rhs :=
    closedForm_solvesNormalEquation ctx
  -- Both costs expand to quadratics in fg/bg; the difference collapses to (g-g*)^T M (g-g*)
  -- after substituting M g' = rhs. We discharge by simp + ring.
  simp only [LocalContext.localCost, LocalContext.compositingResidual_eq,
    LocalContext.normalMatrix_mulVec_foreground, LocalContext.normalMatrix_mulVec_background,
    LocalContext.rhs_foreground, LocalContext.rhs_background] at hsolve ⊢
  have hfg : ctx.normalMatrix.mulVec g' 0 = ctx.rhs 0 := congrFun hsolve 0
  have hbg : ctx.normalMatrix.mulVec g' 1 = ctx.rhs 1 := congrFun hsolve 1
  simp only [LocalContext.normalMatrix_mulVec_foreground,
    LocalContext.normalMatrix_mulVec_background] at hfg hbg
  -- hfg : (α^2 + W)*fg' + α(1-α)*bg' = α*I + fgSum
  -- hbg : α(1-α)*fg' + ((1-α)^2 + W)*bg' = (1-α)*I + bgSum
  simp only [LocalContext.localCost, LocalContext.compositingResidual_eq]
  ring_nf
  nlinarith [hfg, hbg,
    Finset.sum_nonneg (fun j _ => mul_nonneg (neighborWeight_nonneg ctx j) (sq_nonneg _))]
```

> **Note:** If `nlinarith` times out, replace with the explicit algebraic identity:
> add `have hkey : ctx.localCost g - ctx.localCost g' = <rhs_expression> := by ring_nf; linarith [hfg, hbg]`
> and then `exact hkey`.

- [ ] **Step 6: Verify step 5 compiles**

```bash
lake env lean FastMLFE2/Theorems/Solvability/GlobalMinimality.lean
```
Expected: no errors on `localCost_sub_closedForm_eq`.

- [ ] **Step 7: Prove `localCost_closedFormSolution_le`**

Replace its `sorry` with:

```lean
  linarith [localCost_sub_closedForm_eq ctx g,
    normalMatrix_quadratic_form_nonneg ctx
      (mkLocalUnknown
        (foreground g - foreground (closedFormSolution ctx))
        (background g - background (closedFormSolution ctx)))]
```

- [ ] **Step 8: Verify file compiles cleanly (no sorry)**

```bash
lake env lean FastMLFE2/Theorems/Solvability/GlobalMinimality.lean
```
Expected: no errors, no sorry warnings.

- [ ] **Step 9: Add import to FastMLFE2.lean**

Append to `FastMLFE2.lean` (after the existing Solvability imports):

```lean
import FastMLFE2.Theorems.Solvability.GlobalMinimality
```

- [ ] **Step 10: Run full build**

```bash
lake build
```
Expected: Build succeeded. No errors.

- [ ] **Step 11: Commit**

```bash
git add FastMLFE2/Theorems/Solvability/GlobalMinimality.lean FastMLFE2.lean
git commit -m "feat: prove global minimality of closedFormSolution (localCost_closedFormSolution_le)"
```

---

## Task 5 — Connect ContractionBounds to per-pixel Jacobi (early-termination theorem)

`ContractionBounds.lean` provides `scale_mul_pow_le_of_log_threshold` (an iteration budget theorem) but it is stated for abstract `NormedAddCommGroup`. `JacobiContraction.lean` proves concrete error bounds with `localInfinityNorm`. This task adds a bridge theorem that lets callers use the log-threshold formula directly on per-pixel Jacobi.

**Files:**
- **Create:** `FastMLFE2/Theorems/Iteration/JacobiTermination.lean`
- Modify: `FastMLFE2.lean` (add import)

- [ ] **Step 1: Create the file with sorry stub**

Create `FastMLFE2/Theorems/Iteration/JacobiTermination.lean`:

```lean
import FastMLFE2.Theorems.Iteration.JacobiContraction
import FastMLFE2.Theorems.Iteration.ContractionBounds

namespace FastMLFE2.Theorems

/-!
Early-termination iteration budget for per-pixel Jacobi.

Bridges the abstract `scale_mul_pow_le_of_log_threshold` theorem in `ContractionBounds`
to the concrete `jacobiIterate` error bound in `JacobiContraction`.
-/

open FastMLFE2.Core
open FastMLFE2.Core.LocalContext
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- Given an initial error bound `scale` and target tolerance `eta`, the Jacobi
iterate reaches `‖x_k − x*‖∞ ≤ eta` after
  `k ≥ 1 + log(scale / eta) / log(1 / ρ)` steps,
where `ρ = jacobiOneStepGain`. -/
theorem jacobiIterate_terminationBound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    {scale eta : ℝ} (hscale : 0 < scale) (heta : 0 < eta)
    {k : ℕ}
    (hk : 1 + Real.log (scale / eta) / Real.log (1 / jacobiOneStepGain ctx) ≤ (k + 1 : ℝ))
    (hgain_lt : jacobiOneStepGain ctx < 1)
    (x : LocalUnknown)
    (hx : localInfinityNorm (x - closedFormSolution ctx) ≤ scale) :
    localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) ≤ eta := by
  sorry

end LocalContext

end FastMLFE2.Theorems
```

- [ ] **Step 2: Verify sorry file type-checks**

```bash
lake env lean FastMLFE2/Theorems/Iteration/JacobiTermination.lean
```
Expected: no errors.

- [ ] **Step 3: Implement the proof**

Replace `sorry` with:

```lean
  have hgain_nonneg := jacobiOneStepGain_nonneg ctx
  have herr := jacobiIterate_error_le ctx k x
  -- herr : ‖xₖ₊₁ − x*‖∞ ≤ jacobiOneStepGain * jacobiOneStepGain^k * ‖x₀ − x*‖∞
  have hchain : localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx) ≤
      jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k *
        localInfinityNorm (x - closedFormSolution ctx) := herr
  calc localInfinityNorm (jacobiIterate ctx (k + 1) x - closedFormSolution ctx)
      ≤ jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k *
          localInfinityNorm (x - closedFormSolution ctx) := hchain
    _ ≤ jacobiOneStepGain ctx * jacobiOneStepGain ctx ^ k * scale :=
          mul_le_mul_of_nonneg_left hx
            (mul_nonneg hgain_nonneg (pow_nonneg hgain_nonneg _))
    _ = scale * jacobiOneStepGain ctx ^ (k + 1) := by ring
    _ ≤ eta :=
          error_le_of_log_threshold
            (herror := le_refl _)
            hscale heta
            (hrho0 := by linarith)
            (hrho1 := hgain_lt)
            (hk := by
              convert hk using 2
              simp [show (1 : ℝ) / jacobiOneStepGain ctx = (jacobiOneStepGain ctx)⁻¹ from
                one_div _])
```

> **Note:** `error_le_of_log_threshold` is in `ContractionBounds.lean`. If the calc step does not close, replace the last `_ ≤ eta` step with:
>
> ```lean
>     _ ≤ eta := by
>           apply error_le_of_log_threshold (herror := le_refl _) hscale heta
>             (hrho0 := by linarith) (hrho1 := hgain_lt)
>           convert hk using 2; simp [one_div]
> ```

- [ ] **Step 4: Verify compiles cleanly**

```bash
lake env lean FastMLFE2/Theorems/Iteration/JacobiTermination.lean
```
Expected: no errors.

- [ ] **Step 5: Add import to FastMLFE2.lean**

Append to `FastMLFE2.lean`:

```lean
import FastMLFE2.Theorems.Iteration.JacobiTermination
```

- [ ] **Step 6: Run full build**

```bash
lake build
```
Expected: Build succeeded.

- [ ] **Step 7: Commit**

```bash
git add FastMLFE2/Theorems/Iteration/JacobiTermination.lean FastMLFE2.lean
git commit -m "feat: JacobiTermination — bridge ContractionBounds to per-pixel Jacobi"
```

---

## Task 6 — Final integration build and verify

- [ ] **Step 1: Confirm zero sorries**

```bash
python3 "$LEAN4_SCRIPTS/sorry_analyzer.py" FastMLFE2/ --format=json --report-only 2>&1
```
Expected:
```json
{"total_count": 0, "sorries": []}
```

- [ ] **Step 2: Full project build**

```bash
lake build
```
Expected: Build succeeded. No errors.

- [ ] **Step 3: Confirm rawStepGain fix in architecture.md**

```bash
grep "rawStepGain" docs/architecture.md
```
Expected: output contains `rawStepGain ≥ 1`, no `rawStepGain < 1`.

- [ ] **Step 4: Final commit if any stragglers**

```bash
git status --short
```
If clean, nothing to do. If dirty:
```bash
git add -p   # stage only intentional changes
git commit -m "chore: final cleanup after review-gaps plan"
```

---

## Self-Review Checklist

| Gap (from review) | Task | Status |
|---|---|---|
| P0: `rawStepGain < 1` documentation error | Task 1 | ✓ |
| P1: `normalMatrixInv_eq_of_sameWeightData` missing | Task 2 | ✓ |
| P2: compositing residual at solution not stated | Task 3 | ✓ |
| P0: global minimality not formalized | Task 4 | ✓ |
| P1: ContractionBounds not connected to Jacobi | Task 5 | ✓ |
| P2: multi-level convergence not formalized | — | **Deferred** — the multi-level convergence requires a bespoke coarse-to-fine composition theorem that is beyond the scope of these targeted fixes. Recommend tracking as a separate initiative. |

**Deferred item note:** Multi-level cross-scale convergence requires formalizing the upsampling operator semantics and a composition lemma. This is a significant standalone effort. A comment in `FastMLFE2/Canonical/MultilevelSchedule.lean` should be added to document the gap explicitly (out of scope for this plan).
