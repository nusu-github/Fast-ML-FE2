# Fast-ML-FE2

A formalization of Germer et al.'s
[Fast Multi-Level Foreground Estimation](https://doi.org/10.1109/ICIP46576.2022.9897331)
in **Lean 4** (Dependent Type Theory), targeting **proof-directed optimal implementation
derivation** through a three-stage pipeline.

## Overview

This project builds a **parametric theory** of alpha-matting foreground estimation on Lean 4
with Mathlib. The algorithm's mathematical skeleton — the local cost function
$\mathcal{L}_{\text{local}}$, the 2×2 normal equation, and the multilevel coarse-to-fine
pyramid — is expressed as **denotational semantics** in Lean. Hardware and algorithmic
constraints (floating-point precision, SIMD width, warp size, neighborhood stencil, etc.)
are injected as **parameterized axiom bundles** (`class` / `structure` typeclasses), yielding
a switchable parametric theory.

### Three-Stage Pipeline

| Stage | Name                                          | Description                                                                                                                                                                                                                                |
| ----- | --------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **1** | **Formal Specification**                      | Denotational semantics of the cost function, normal-equation derivation, and multilevel recursion. Axiom bundles parameterize hardware/algorithmic constraints.                                                                            |
| **2** | **Formal Design-Space Exploration**           | Conditional equational theorems for each axiom instantiation — e.g. binary α ⇒ diagonal degeneration; channel independence ⇒ shared matrix reuse; ε_r > 0 ⇒ positive definiteness. Exhaustive verification over the assumption lattice.    |
| **3** | **Deductive Synthesis (Stepwise Refinement)** | Proved equalities serve as rewrite rules to transform the abstract spec into efficient forms: closed-form 2×2 inverse, loop fusion, Jacobi-parallel pixel independence. Each step is a **certified refinement** (Correct-by-Construction). |

### Project Structure

`FastMLFE2` is the main library target.
See [docs/architecture.md](docs/architecture.md) for the layered design.

## Module Map

```txt
FastMLFE2.lean                          ← umbrella import
FastMLFE2/
├── Core/
│   ├── LocalEquation.lean          ← local context, cost, normal matrix, RHS
│   └── LocalSemantics.lean         ← solution / stationarity relations
├── Compositing/
│   └── OneChannel.lean             ← α·F + (1-α)·B semantics
├── Canonical/
│   ├── Builder.lean                ← CanonicalPixelData; canonical builder construction
│   ├── Grid.lean                   ← Fin h × Fin w geometry, four-connected neighborhoods
│   ├── GridContext.lean            ← GridPixelData.localCtx aliases
│   ├── InteriorKernel.lean         ← interior-pixel specialized context and closed-form solver
│   ├── ClampPlacement.lean         ← projection variants (raw / inside-clamped / end-clamped)
│   ├── LocalCommitments.lean       ← stencil, resize rule, iteration semantics
│   └── MultilevelSchedule.lean     ← level-size computation
├── Approximation/
│   └── BlurFusion.lean             ← idealized PhotoRoom Blur-Fusion surrogate
├── Assumptions/
│   ├── Bundles.lean                ← CoreMathAssumptions, variant bundles
│   └── Grid.lean                   ← GridMathAssumptions, bridge to CoreMathAssumptions
└── Theorems/
    ├── Invertibility.lean          ← det > 0, IsUnit det
    ├── ClosedForm.lean             ← explicit 2×2 inverse, uniqueness
    ├── ClosedFormBox.lean          ← conditional [0,1] membership from numerator bounds
    ├── ClosedFormBoxInput.lean     ← mean-affine form; counterexample for naive box-input
    ├── ClosedFormMeanResidual.lean ← meanResidual-corrected solution characterization
    ├── NormalizedWeights.lean      ← normalized weight form of fore-/backgroundMean
    ├── CostToNormalEquation.lean   ← ∂cost/∂t = 0 ↔ normal equation
    ├── Conditioning.lean           ← eigenvalues, κ = 1 + q(α)/s
    ├── BinaryAlpha.lean            ← normalMatrix / rhs degenerations for α ∈ {0, 1}
    ├── BinaryAlphaCost.lean        ← localCost and stationarity for binary α
    ├── ChannelReuse.lean           ← SameWeightData; matrix coefficient invariance across channels
    ├── ClampLocal.lean             ← clamp01 self-identity and nonexpansiveness
    ├── JacobiContraction.lean      ← jacobiStep, spectral radius, contraction bound
    ├── ClampPlacement.lean         ← clamp ordering (inside vs end) and rawStepGain
    ├── ClampPlacementCounterexample.lean ← inside-clamped ≠ end-clamped witness
    ├── MeanResidualBounds.lean     ← mean residual bounds and correction terms
    ├── ResidualCompositeBounds.lean  ← closed-form composite error vs mean residual
    ├── ContractionBounds.lean      ← relaxed updates, λ_max, and iteration budgets
    ├── NearBinary.lean             ← meanResidual correction around weighted means
    ├── NearBinaryCounterexample.lean ← clamp-binary swap counterexample
    ├── IterationInvariance.lean    ← weight/matrix coefficients state-independent in canonical builders
    ├── BleedThrough.lean           ← component-wise Jacobi iterate error vs closed form
    ├── BlurFusionGap.lean          ← synthetic Blur-Fusion stage-two context; joint vs sequential gap
    ├── BlurFusionFixedPoint.lean   ← Blur-Fusion x1 fixed-point counterexample
    ├── PropagationRadius.lean      ← k-pass locality / support growth bounds
    ├── SpatialDecay.lean           ← abstract radius-decay and halo-width interfaces
    ├── CompositingError.lean       ← |Δcompose| ≤ α|ΔF| + (1-α)|ΔB|
    ├── Jacobi.lean                 ← pointwise Jacobi lifting to closed-form solutions
    ├── Locality.lean               ← builder locality lifts to jacobiUpdateAt / jacobiStep
    ├── Grid.lean                   ← faithful 2D four-neighbor geometry theorems
    ├── GridNonempty.lean           ← constructive ValidDir nonemptiness witnesses
    ├── GridAssumptions.lean        ← GridMathAssumptions → CoreMathAssumptions bridge
    ├── GridLocal.lean              ← closed-form theorems on GridPixelData.localCtx
    ├── InteriorKernel.lean         ← closed-form theorems on interior-pixel context
    └── CanonicalBuilder.lean       ← field-correctness for canonical builders
```

Experimental modules (not part of the default umbrella import):

```txt
FastMLFE2/
├── GlobalSystem.lean               ← global block linear system; weighted Laplacian,
│                                     globalLinearResidual, bridge to local residuals
└── MultigridSpec.lean              ← abstract V-cycle skeleton (GridTransfer, VCycleOps)
                                      and fixed-point theorem (work in progress)
```

## Proved Theorems

The theory layer currently contains the following machine-checked results, mapped to the
pipeline stages:

**Stage 1 (Formal Specification):**

- Local cost function, 2×2 normal matrix, and RHS vector (`Core.LocalEquation`)
- Solution / stationarity relations (`Core.LocalSemantics`)
- Canonical commitments: 4-connected stencil, nearest-neighbor resize, deterministic
  simultaneous update (`Canonical`)
- Idealized Blur-Fusion approximation semantics (`Approximation.BlurFusion`)

**Stage 2 (Design-Space Exploration):**

- **Invertibility** — ε_r > 0 ⇒ neighbor weights positive; `totalWeight > 0`; normal
  matrix determinant positive and a unit.
- **Local Conditioning** — Normal matrix decomposes as `s·I + u·uᵀ` (rank-1 update);
  exact eigenvalues `s` and `s + q(α)` where `q(α) = α² + (1−α)²`; condition number
  `κ = 1 + q(α)/s` with bounds `1 + 1/(2s) ≤ κ ≤ 1 + 1/s`.
- **Relaxation Bounds** — relaxed updates contract for `0 < λ < λ_max = 2/(1+q)`;
  a scalar sign-flip example shows the bound is sharp.
- **Normalized-Weight Means** — With `λ_j = w_j / W`, the weighted means admit equivalent
  forms `foregroundMean = ∑ j, λ_j F_j` and `backgroundMean = ∑ j, λ_j B_j`; normalized
  weights sum to `1`.
- **Binary-α Degenerations** — Normal matrix, RHS, and `closedFormDenom` simplifications
  for `α = 0` and `α = 1`; corresponding cost-function forms and stationarity conditions.
- **Channel Coefficient Invariance** — `SameWeightData` predicate captures shared α, ε_r, ω
  across channels; proves normal matrix, `totalWeight`, and `weightedMeanDenom` are identical
  across same-weight contexts. Formally guarantees shared-matrix reuse in RGB processing.
- **Compositing Error** — `|compose α F B − compose α F' B'| ≤ |α|·|F−F'| + |1−α|·|B−B'|`;
  authored corollary with simplified weights when `0 ≤ α ≤ 1`.
- **MeanResidualBounds** — `|meanResidual| ≤ 1` under boxed inputs; foreground/background
  correction bounds.
- **ResidualCompositeBounds** — exact compositing error in terms of `meanResidual`; finite-family
  infinity-norm corollary.
- **Blur-Fusion Stage-Two Gap** — Synthetic `blurStageTwoCtx` whose local cost equals the
  Blur-Fusion stage-two surrogate; exact joint minimizer derived and compared with the
  sequential stage-two output; gap between joint and sequential solutions quantified.
- **Blur-Fusion Fixed-Point Counterexample** — Explicit one-pixel witness showing the
  Blur-Fusion `x1` update is generally not a fixed point; update differs from the canonical
  closed-form Jacobi step.
- **Near-Binary Clamp Counterexample** — Numerical witness refuting a naive claim that
  clamping and binary-α substitution can be swapped.
- **Iteration Weight Invariance** — In a `CanonicalPixelData` builder, neighbor weights,
  `totalWeight`, and `weightedMeanDenom` are independent of the current pixel state
  (`totalWeight_eq_of_build`, `weightedMeanDenom_eq_of_build`).

**Stage 3 (Deductive Synthesis):**

- **Closed-Form Solution** — Explicit 2×2 inverse solves the normal equation (det ≠ 0
  proof); solution is unique; equals matrix-inverse form.
- **Conditional Solution Bounds** — Closed-form solution lies in `[0,1]` componentwise when
  numerator bounds are satisfied; `clamp01` acts as identity on valid inputs.
- **Mean-Affine Solution Form** — Closed-form solution expressed as
  `foregroundMean + α·meanResidual / denom`; counterexample showing the naive box-input
  `[0,1]` claim fails without additional hypotheses.
- **Closed-Form Mean-Residual Characterization** — `meanResidualSolution` exposes the shared
  `meanResidual` correction; by uniqueness this form characterizes any normal-equation solution
  (`ClosedFormMeanResidual`).
- **Near-Binary Mean-Residual Correction** — The closed-form updates are weighted means plus
  a shared `meanResidual`; by uniqueness the same correction characterizes any solution.
- **Cost–Normal-Equation Bridge** — Local cost expands as a quadratic in perturbation `t`;
  genuine `HasDerivAt` derivatives; `IsCostStationary ↔ SolvesNormalEquation`.
- **clamp01 Nonexpansiveness** — `clamp01Scalar` and component-wise `clamp01` are
  non-expanding under the infinity norm (`ClampLocal`).
- **Jacobi Contraction** — Local Jacobi step has spectral radius
  `ρ = jacobiCrossTerm / √(diagFg · diagBg) < 1` under `CoreMathAssumptions`; error
  contracts geometrically with each step.
- **Clamp Placement Ordering** — `rawStepGain < 1` under `CoreMathAssumptions`; inside-clamped
  and end-clamped iterates are provably distinct (explicit counterexample).
- **Jacobi Bleed-Through Bounds** — Component-wise error bound
  `|fg_k − fg*| ≤ jacobiOneStepGain × ρ^(k−1) × ‖x₀ − x*‖∞` (`BleedThrough`).
- **Propagation Radius Bounds** — fixed-level Jacobi and Blur-Fusion `k`-pass outputs depend
  only on the recursively expanded `k`-hop neighborhood induced by the builder locality law.
- **SpatialDecay** — abstract exponential radius-decay and fixed-exterior halo envelopes.
- **Iteration Budgets** — `E₀ q^k ≤ η` gives a sufficient early-termination threshold via a
  reusable log-based theorem.

## Prerequisites

- **Lean 4** — version specified in `lean-toolchain` (currently `v4.28.0`)
- **Mathlib** — fetched automatically by Lake (`v4.28.0`)

## Build

```sh
# Build the library
lake build

# Type-check a single file
lake env lean FastMLFE2/Theorems/Invertibility.lean
```

## Project Structure

| Path              | Role                                                        |
| ----------------- | ----------------------------------------------------------- |
| `FastMLFE2/`      | Main Lean source modules                                    |
| `docs/`           | Architecture and design documents ([index](docs/README.md)) |
| `evaluation/`     | Evaluation scripts                                          |
| `lakefile.toml`   | Lake build configuration                                    |
| `lean-toolchain`  | Lean version pin                                            |

## Dependencies

| Dependency                                                  | Version | Purpose                                       |
| ----------------------------------------------------------- | ------- | --------------------------------------------- |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | v4.28.0 | Linear algebra, analysis, real number library |
| [REPL](https://github.com/leanprover-community/repl)        | v4.28.0 | Interactive Lean REPL support                 |

## License

See repository for license information.
