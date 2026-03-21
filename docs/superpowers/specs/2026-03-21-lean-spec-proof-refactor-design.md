# Lean Spec Proof Refactor Design

## Goal

Refactor the Lean `spec` layer so that proofs become shorter, more local, and more mathlib-oriented without changing any theorem statements, definitions, or executable behavior.

The immediate target is proof simplification, not API redesign.

## Scope

In scope:

- `FastMLFE2/LinearAlgebra.lean`
- `FastMLFE2/SummaryForm.lean`
- small follow-on cleanup in `FastMLFE2/MultilevelSpec.lean` if simplification lemmas naturally help there

Out of scope:

- changes to theorem statements or public definitions
- `reference` runtime code
- FFI, CLI, or native solver changes
- semantic changes to the local solver model

## Current Pain Points

### `LinearAlgebra.lean`

The main equalities between paper-level matrix expressions and reduced closed forms are currently proved by expanding matrix entries manually. The pattern

- define an intermediate matrix
- prove `h00`, `h01`, `h10`, `h11`
- finish by `ext` and `fin_cases`

works, but it makes the file longer than necessary and duplicates the same algebraic reasoning in multiple places.

### `SummaryForm.lean`

The summary proofs mostly transport results through `closedForm` and then restate equalities componentwise. This is correct, but some proofs are more procedural than needed and rely on repeating expansion details already available upstream.

## Recommended Approach

Use a helper-lemma extraction strategy.

Add a small number of focused lemmas in `LinearAlgebra.lean` that expose the structure of the two important paper expressions:

- `((broadcastMatrixᵀ) * weightMatrix * broadcastMatrix)` contributes `totalWeight` on the diagonal and `0` off-diagonal
- `((broadcastMatrixᵀ) * weightMatrix).mulVec neighborVec` yields `foregroundSum` and `backgroundSum`

Then rewrite the downstream theorems so they depend on those lemmas via `simp`, `simpa`, and short algebraic closing steps.

This is preferred over a pure `@[simp]` spray because it keeps the proof story explicit, and preferred over a full matrix-level reformulation because the latter is likely to cost more effort than it saves in this codebase.

## Design

### 1. Add structural helper lemmas in `LinearAlgebra.lean`

Introduce intermediate lemmas with names that reflect the paper objects, for example:

- a lemma for each entry of the weighted broadcast product
- a lemma for each component of the weighted broadcast right-hand side

These lemmas should be the only place where the heavy matrix expansion lives. They can still use `simp` with `Matrix.mul_apply`, `Matrix.diagonal`, `Fintype.sum_sum_type`, and `fin_cases`, but the complexity will be isolated.

### 2. Rewrite top-level equality theorems to consume helpers

Refactor:

- `paperSystemMatrix_eq_systemMatrix`
- `paperRhs_eq_rhs`

so they no longer locally introduce `h00`, `h01`, `h10`, `h11` or duplicate expansion work inline. The target shape is:

- obtain component lemmas
- `ext i j` or `ext i`
- finish by `simp` and one small algebraic step if needed

### 3. Simplify transport proofs in `SummaryForm.lean`

Refactor:

- `closedForm_foreground_eq_summary`
- `closedForm_background_eq_summary`
- `closedForm_eq_summaryUpdate`
- `summaryUpdate_solves_localSystem`
- `summaryUpdate_stationary`

to rely more directly on the improved upstream equalities and existing projection lemmas. Prefer `simpa` over manual `rw` chains where the proof is a direct transport.

### 4. Keep `MultilevelSpec.lean` opportunistic only

If the upstream simplifications yield direct shorter proofs in `MultilevelSpec.lean`, apply them. Otherwise leave the file unchanged.

## Expected File Shape After Refactor

`LinearAlgebra.lean` should become the canonical place for paper-to-reduced linear algebra identities.

`SummaryForm.lean` should read as a thin consequence layer:

- define summary expressions
- prove projections
- prove equality with `closedForm`
- inherit solver and stationarity facts

This keeps algebraic expansion low in the stack and semantic consequences high in the stack.

## Error Handling

The refactor must preserve these constraints:

- no theorem statement changes
- no new axioms
- no `sorry`
- no broad `simp` attributes that create brittle global behavior

If a helper lemma does not actually shorten downstream proofs, it should be removed instead of kept as unused abstraction.

## Testing And Verification

Verification should be incremental:

1. Use Lean diagnostics on each edited file while refactoring.
2. Run `lake env lean FastMLFE2/LinearAlgebra.lean`.
3. Run `lake env lean FastMLFE2/SummaryForm.lean`.
4. Run `lake build` as the final gate.

Success criteria:

- project builds cleanly
- no statement changes
- proof terms are shorter or structurally clearer in the targeted theorems
- no new warnings or axioms

## Implementation Plan Handoff

The implementation plan should follow this order:

1. Refactor `LinearAlgebra.lean` helper structure first.
2. Refactor `SummaryForm.lean` to consume the helpers.
3. Apply any trivial cleanup in `MultilevelSpec.lean`.
4. Run file-level verification, then full project verification.
