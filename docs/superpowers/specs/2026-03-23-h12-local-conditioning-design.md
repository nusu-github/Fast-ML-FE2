# H12 Local Conditioning Design

## Goal

Add a theory-first theorem module that formalizes the local conditioning structure of the
single-pixel 2x2 normal matrix. The target is H12 alone: derive the canonical spectral form of
the local matrix, prove the exact 2-norm condition number formula, and prove how that condition
number varies with `alphaCenter`.

This design deliberately stays inside the existing local kernel. It does not introduce level
semantics, finite-iteration semantics, backend schedule semantics, or visual-quality claims.

## Scope

In scope:

- the canonical algebraic form `A = s I + u u^T`
- the scalar profile `q(alpha) = alpha^2 + (1 - alpha)^2`
- the exact local eigenvalue pair
- the exact local 2-norm condition number formula
- the extremum facts on `alpha ∈ [0,1]`

Out of scope:

- perturbation bounds for `δb -> δg`
- floating-point roundoff analysis
- clamp-inside vs clamp-outside iteration theorems
- recomposition error theorems (`H11a`)
- bleed-through / propagation theorems (`H11b`)
- one-level or multilevel iteration semantics

## Architecture

The design adds a new theorem-only module:

- `FastMLFE2/Theory/Theorems/Conditioning.lean`

No new core definitions are required. The module sits on top of:

- `FastMLFE2/Theory/Core/LocalEquation.lean`
- `FastMLFE2/Theory/Assumptions/Bundles.lean`
- `FastMLFE2/Theory/Theorems/Invertibility.lean`

The theorem module is imported by:

- `FastMLFE2/Theory.lean`

The implementation strategy is `spectral-first`, not `formula-only`. The key idea is to expose
the local normal matrix in the canonical rank-1 update form

`A = s I + u u^T`

with `s = totalWeight` and `u = [alpha, 1 - alpha]^T`. Once this is proved, the local spectrum,
condition number, and `alpha`-dependence become short corollaries instead of isolated algebraic
manipulations.

## Module Contents

`Conditioning.lean` should contain four groups of theorems.

### 1. Algebraic Normal Form

These theorems rewrite the existing local matrix into the canonical form used by H12.

- `normalMatrix_eq_totalWeight_mul_I_add_uOuter`
- `uVec_dot_uVec_eq_alphaQuadratic`

The first theorem should present the matrix as `ctx.totalWeight • 1 + col u * row u` or an
equivalent `Fin 2` formulation that is convenient in Lean. The exact encoding may follow
whatever is easiest to prove with mathlib's matrix primitives, but the theorem statement should
make the rank-1 update structure explicit.

### 2. Alpha Quadratic Profile

Introduce a theorem-level helper quantity:

- `alphaQuadratic := ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2`

This does not need to become a new core definition unless proof ergonomics clearly justify it.
The main facts are:

- `alphaQuadratic_eq_two_mul_sq_sub_two_mul_add_one`
- `one_half_le_alphaQuadratic`
- `alphaQuadratic_le_one`
- `alphaQuadratic_eq_one_half_iff_alpha_half` or a weaker minimizer statement
- endpoint-max corollaries at `alpha = 0` and `alpha = 1`

These theorems should depend only on the boundedness assumption already present in
`CoreMathAssumptions`.

### 3. Spectral Facts

Avoid a heavy general spectral theorem path. This is a `Fin 2` matrix, so use the explicit
rank-1 structure.

The desired end result is:

- `normalMatrix_minEigenvalue_eq_totalWeight`
- `normalMatrix_maxEigenvalue_eq_totalWeight_add_alphaQuadratic`

Whether these are stated using `Matrix.IsEigenvalue`, a characteristic-polynomial argument, or an
explicit 2x2 symmetric-matrix eigenvalue calculation is an implementation choice. The design
preference is to stay as concrete as possible and avoid introducing broad linear-algebra
abstractions that are not reused elsewhere in the project.

### 4. Conditioning Theorems

These are the actual H12 outputs.

- `normalMatrix_conditionNumber_eq`
- `normalMatrix_conditionNumber_eq_one_add_alphaQuadratic_div_totalWeight`
- `normalMatrix_conditionNumber_lower_bound`
- `normalMatrix_conditionNumber_upper_bound`
- `normalMatrix_conditionNumber_min_at_alpha_half`
- `normalMatrix_conditionNumber_max_at_alpha_extremes`

The main exact formula should be:

`κ₂(A) = (s + q(alpha)) / s = 1 + q(alpha) / s`

with `s = ctx.totalWeight` and `q(alpha) = alpha^2 + (1 - alpha)^2`.

The bound corollaries on `alpha ∈ [0,1]` should expose:

- best case: `1 + 1 / (2s)`
- worst case: `1 + 1 / s`

The exact equality cases should be kept separate from the coarse bounds so theorem statements stay
clean.

## Proof Strategy

The recommended proof order is:

1. reuse `normalMatrix_det` and `totalWeight_pos` from `Invertibility.lean`
2. prove the rank-1 normal form
3. prove the scalar `alphaQuadratic` bounds on `[0,1]`
4. derive the eigenvalues in the concrete 2x2 setting
5. derive the exact condition-number formula
6. derive the extremum corollaries

The critical design choice is to avoid turning H12 into an isolated symbolic proof. The local
matrix should emerge in a form that will later support:

- Sherman-Morrison style inverse derivations
- sensitivity bounds
- backend-oriented algebraic rewrites

## Testing and Verification

The implementation should follow a theorem-level RED/GREEN flow.

Expected verification commands:

- `lake env lean FastMLFE2/Theory/Theorems/Conditioning.lean`
- `lake env lean FastMLFE2/Theory.lean`
- `lake build FastMLFE2`
- `git diff --check`

The file should compile without new warnings in the edited module.

## Non-Goals and Follow-On Work

This design intentionally does not claim that worst local conditioning immediately implies worst
visual output. That bridge requires additional theorems.

Planned later layers:

- `H11a`: recomposition-error bounds in a compositing semantics module
- `H5-local`: local clamp invariance criteria
- `H5-global`: iteration-level clamp placement comparison, after level semantics exist
- `H11b`: propagation / bleed-through guarantees, after 1-level Jacobi semantics exist

So H12 is treated here as a local numerical-structure theorem, not yet as a full quality theorem.
