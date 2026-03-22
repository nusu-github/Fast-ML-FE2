# H12 Local Conditioning Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a local-theory theorem module that proves the H12 conditioning structure of the single-pixel 2x2 normal matrix.

**Architecture:** Implement H12 as a standalone theorem module on top of the existing local kernel. The proof flow is spectral-first: first expose the local matrix as `s I + u u^T`, then prove the `alpha` quadratic profile, then prove explicit eigenvector/eigenvalue witnesses in `Fin 2`, and only then derive the conditioning corollaries.

**Tech Stack:** Lean 4, mathlib4 matrix algebra, existing `FastMLFE2.Theory` local-kernel theorem modules.

---

## Chunk 1: Create the H12 Theorem Module and Prove the Algebraic Normal Form

### Task 1: Add the new theorem module and prove the rank-1 update form

**Files:**
- Create: `FastMLFE2/Theory/Theorems/Conditioning.lean`
- Modify: `FastMLFE2/Theory.lean`
- Reference: `FastMLFE2/Theory/Core/LocalEquation.lean`
- Reference: `FastMLFE2/Theory/Theorems/Invertibility.lean`
- Test: `FastMLFE2/Theory/Theorems/Conditioning.lean`

- [ ] **Step 1: Add the new theorem module import to the theory umbrella**

Update `FastMLFE2/Theory.lean` to add:

```lean
import FastMLFE2.Theory.Theorems.Conditioning
```

- [ ] **Step 2: Create a failing theorem skeleton for the new module**

Create `FastMLFE2/Theory/Theorems/Conditioning.lean` with:

```lean
import FastMLFE2.Theory.Theorems.Invertibility

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

private def alphaQuadratic (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2

private def orthVec (ctx : LocalContext ι) : LocalUnknown :=
  ![1 - ctx.alphaCenter, -ctx.alphaCenter]

theorem normalMatrix_eq_totalWeight_plus_uOuter
    (ctx : LocalContext ι) :
    ctx.normalMatrix =
      ![![ctx.totalWeight + ctx.alphaCenter ^ 2,
          ctx.alphaCenter * (1 - ctx.alphaCenter)],
        ![ctx.alphaCenter * (1 - ctx.alphaCenter),
          ctx.totalWeight + (1 - ctx.alphaCenter) ^ 2]] := by
  sorry

end LocalContext

end FastMLFE2.Theory.Theorems
```

- [ ] **Step 3: Run the new theorem file and confirm it fails on the skeleton**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: FAIL with an unsolved goal in `normalMatrix_eq_totalWeight_plus_uOuter`

- [ ] **Step 4: Prove the matrix normal-form theorem**

Prove `normalMatrix_eq_totalWeight_plus_uOuter` by unfolding `LocalContext.normalMatrix` and
using `ext i j <;> fin_cases i <;> fin_cases j <;> simp`.

Do not introduce a new core matrix definition. Keep the theorem at the theorem-module layer.

- [ ] **Step 5: Add a second normal-form theorem that explicitly packages the `u u^T` shape**

Add:

```lean
theorem normalMatrix_eq_totalWeight_plus_uOuter'
    (ctx : LocalContext ι) :
    ctx.normalMatrix =
      ![![ctx.totalWeight + (uVec ctx.alphaCenter 0) * (uVec ctx.alphaCenter 0),
          (uVec ctx.alphaCenter 0) * (uVec ctx.alphaCenter 1)],
        ![(uVec ctx.alphaCenter 1) * (uVec ctx.alphaCenter 0),
          ctx.totalWeight + (uVec ctx.alphaCenter 1) * (uVec ctx.alphaCenter 1)]] := by
  sorry
```

Keep this theorem only if it materially helps later proofs. If the first normal-form theorem
already gives the cleanest basis for the later chunks, delete this second skeleton instead of
carrying dead weight.

- [ ] **Step 6: Re-run the conditioning module**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: PASS

- [ ] **Step 7: Commit the new module and algebraic normal form**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Theorems/Conditioning.lean
git commit -m "feat: add local conditioning normal-form theorems"
```

## Chunk 2: Prove the Alpha Quadratic Profile

### Task 2: Formalize the `alpha^2 + (1-alpha)^2` profile used by H12

**Files:**
- Modify: `FastMLFE2/Theory/Theorems/Conditioning.lean`
- Reference: `FastMLFE2/Theory/Assumptions/Bundles.lean`
- Test: `FastMLFE2/Theory/Theorems/Conditioning.lean`

- [ ] **Step 1: Add a failing identity skeleton for the alpha profile**

Add:

```lean
theorem alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one
    (ctx : LocalContext ι) :
    alphaQuadratic ctx =
      2 * ctx.alphaCenter ^ 2 - 2 * ctx.alphaCenter + 1 := by
  sorry
```

- [ ] **Step 2: Run the conditioning module and confirm the new skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: FAIL with an unsolved goal in `alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one`

- [ ] **Step 3: Prove the polynomial identity**

Use:

```lean
simp [alphaQuadratic]
ring
```

- [ ] **Step 4: Add the boundedness theorems on `[0, 1]`**

Add:

```lean
theorem one_half_le_alphaQuadratic
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    (1 : ℝ) / 2 ≤ alphaQuadratic ctx := by
  sorry

theorem alphaQuadratic_le_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    alphaQuadratic ctx ≤ 1 := by
  sorry
```

Use `CoreMathAssumptions.alphaCenterBounded`, the polynomial identity from Step 3, and
`nlinarith`.

- [ ] **Step 5: Add endpoint exact-value corollaries**

Add:

```lean
theorem alphaQuadratic_eq_one_of_alpha_zero
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 0) :
    alphaQuadratic ctx = 1 := by
  sorry

theorem alphaQuadratic_eq_one_of_alpha_one
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = 1) :
    alphaQuadratic ctx = 1 := by
  sorry

theorem alphaQuadratic_eq_one_half_of_alpha_half
    (ctx : LocalContext ι)
    (hα : ctx.alphaCenter = (1 : ℝ) / 2) :
    alphaQuadratic ctx = (1 : ℝ) / 2 := by
  sorry
```

- [ ] **Step 6: Re-run the conditioning module**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: PASS

- [ ] **Step 7: Commit the alpha-profile theorems**

```bash
git add FastMLFE2/Theory/Theorems/Conditioning.lean
git commit -m "feat: prove alpha quadratic profile for h12"
```

## Chunk 3: Prove Explicit Spectral Witnesses in `Fin 2`

### Task 3: Show the local matrix acts diagonally on the two canonical directions

**Files:**
- Modify: `FastMLFE2/Theory/Theorems/Conditioning.lean`
- Test: `FastMLFE2/Theory/Theorems/Conditioning.lean`

- [ ] **Step 1: Add a failing eigenvector-action skeleton for `uVec`**

Add:

```lean
theorem normalMatrix_mulVec_uVec
    (ctx : LocalContext ι) :
    ctx.normalMatrix.mulVec (uVec ctx.alphaCenter) =
      fun i => (ctx.totalWeight + alphaQuadratic ctx) * uVec ctx.alphaCenter i := by
  sorry
```

- [ ] **Step 2: Run the conditioning module and confirm the skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: FAIL with an unsolved goal in `normalMatrix_mulVec_uVec`

- [ ] **Step 3: Prove the `uVec` action theorem**

Use:

- `ext i`
- `fin_cases i`
- `normalMatrix_mulVec_foreground`
- `normalMatrix_mulVec_background`
- `foreground_uVec`
- `background_uVec`
- `alphaQuadratic`
- `ring`

- [ ] **Step 4: Add a failing eigenvector-action skeleton for `orthVec`**

Add:

```lean
theorem normalMatrix_mulVec_orthVec
    (ctx : LocalContext ι) :
    ctx.normalMatrix.mulVec (orthVec ctx) =
      fun i => ctx.totalWeight * orthVec ctx i := by
  sorry
```

- [ ] **Step 5: Run the conditioning module and confirm the second skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: FAIL with an unsolved goal in `normalMatrix_mulVec_orthVec`

- [ ] **Step 6: Prove the `orthVec` action theorem**

Use the same style as Step 3 with `ext i`, `fin_cases i`, and `ring`.

- [ ] **Step 7: Prove the two witness vectors are nonzero under the needed hypotheses**

Add:

```lean
theorem uVec_ne_zero
    (ctx : LocalContext ι) :
    uVec ctx.alphaCenter ≠ 0 := by
  sorry

theorem orthVec_ne_zero
    (ctx : LocalContext ι) :
    orthVec ctx ≠ 0 := by
  sorry
```

The expected proof style is `intro h`, evaluate one coordinate, and close with `nlinarith`.
If either theorem needs the boundedness assumption to exclude a degenerate case, add
`[CoreMathAssumptions ctx]` and document that choice in the code comment above the theorem.

- [ ] **Step 8: Package the action theorems as explicit local eigenvalue witnesses**

Add:

```lean
theorem totalWeight_is_local_eigenvalue
    (ctx : LocalContext ι) :
    ∃ v : LocalUnknown, v ≠ 0 ∧
      ctx.normalMatrix.mulVec v = fun i => ctx.totalWeight * v i := by
  refine ⟨orthVec ctx, orthVec_ne_zero ctx, ?_⟩
  simpa using normalMatrix_mulVec_orthVec ctx

theorem totalWeight_add_alphaQuadratic_is_local_eigenvalue
    (ctx : LocalContext ι) :
    ∃ v : LocalUnknown, v ≠ 0 ∧
      ctx.normalMatrix.mulVec v = fun i => (ctx.totalWeight + alphaQuadratic ctx) * v i := by
  refine ⟨uVec ctx.alphaCenter, uVec_ne_zero ctx, ?_⟩
  simpa using normalMatrix_mulVec_uVec ctx
```

These witness the exact spectral pair without forcing the plan onto a heavy general-eigenvalue API.

- [ ] **Step 9: Re-run the conditioning module**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: PASS

- [ ] **Step 10: Commit the spectral witness theorems**

```bash
git add FastMLFE2/Theory/Theorems/Conditioning.lean
git commit -m "feat: add local spectral witnesses for h12"
```

## Chunk 4: Derive the Conditioning Formula and Extremum Corollaries

### Task 4: Package the H12 formula and its `alpha`-dependence

**Files:**
- Modify: `FastMLFE2/Theory/Theorems/Conditioning.lean`
- Test: `FastMLFE2/Theory/Theorems/Conditioning.lean`
- Test: `FastMLFE2/Theory.lean`

- [ ] **Step 1: Add a theorem-level local conditioning quantity**

Add:

```lean
def localConditionNumber (ctx : LocalContext ι) : ℝ :=
  (ctx.totalWeight + alphaQuadratic ctx) / ctx.totalWeight
```

Keep it inside `Conditioning.lean`. Do not add it to `Core`.

- [ ] **Step 2: Add a failing formula skeleton**

Add:

```lean
theorem localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    localConditionNumber ctx =
      1 + alphaQuadratic ctx / ctx.totalWeight := by
  sorry
```

- [ ] **Step 3: Run the conditioning module and confirm the formula skeleton fails**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: FAIL with an unsolved goal in `localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight`

- [ ] **Step 4: Prove the exact conditioning formula**

Use `field_simp` only if needed. Prefer:

```lean
have htw : ctx.totalWeight ≠ 0 := (totalWeight_pos ctx).ne'
field_simp [localConditionNumber, htw]
ring
```

- [ ] **Step 5: Add the coarse lower and upper bounds**

Add:

```lean
theorem localConditionNumber_lower_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    1 + ((1 : ℝ) / 2) / ctx.totalWeight ≤ localConditionNumber ctx := by
  sorry

theorem localConditionNumber_upper_bound
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    localConditionNumber ctx ≤ 1 + 1 / ctx.totalWeight := by
  sorry
```

Prove them from:

- `localConditionNumber_eq_one_add_alphaQuadratic_div_totalWeight`
- `one_half_le_alphaQuadratic`
- `alphaQuadratic_le_one`
- `totalWeight_pos`

- [ ] **Step 6: Add the exact midpoint and endpoint conditioning corollaries**

Add:

```lean
theorem localConditionNumber_eq_best_case_of_alpha_half
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = (1 : ℝ) / 2) :
    localConditionNumber ctx = 1 + ((1 : ℝ) / 2) / ctx.totalWeight := by
  sorry

theorem localConditionNumber_eq_worst_case_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 0) :
    localConditionNumber ctx = 1 + 1 / ctx.totalWeight := by
  sorry

theorem localConditionNumber_eq_worst_case_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hα : ctx.alphaCenter = 1) :
    localConditionNumber ctx = 1 + 1 / ctx.totalWeight := by
  sorry
```

- [ ] **Step 7: Add the human-facing H12 summary theorem**

Add one short corollary that packages the practical result:

```lean
theorem localConditionNumber_bounds
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    1 + ((1 : ℝ) / 2) / ctx.totalWeight ≤ localConditionNumber ctx ∧
      localConditionNumber ctx ≤ 1 + 1 / ctx.totalWeight := by
  exact ⟨localConditionNumber_lower_bound ctx, localConditionNumber_upper_bound ctx⟩
```

- [ ] **Step 8: Re-run the conditioning module**

Run: `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
Expected: PASS

- [ ] **Step 9: Re-run the theory umbrella**

Run: `lake env lean FastMLFE2/Theory.lean`
Expected: PASS

- [ ] **Step 10: Run the full theory build**

Run: `lake build FastMLFE2`
Expected: PASS with no new warnings in `Conditioning.lean`

- [ ] **Step 11: Run the diff check**

Run: `git diff --check`
Expected: PASS

- [ ] **Step 12: Commit the conditioning corollaries**

```bash
git add FastMLFE2/Theory.lean FastMLFE2/Theory/Theorems/Conditioning.lean
git commit -m "feat: prove h12 local conditioning structure"
```
