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
│   ├── LocalCommitments.lean       ← stencil, resize rule, iteration semantics
│   └── MultilevelSchedule.lean     ← level-size computation
├── Approximation/
│   └── BlurFusion.lean             ← idealized PhotoRoom Blur-Fusion surrogate
├── Assumptions/
│   └── Bundles.lean                ← CoreMathAssumptions, variant bundles
└── Theorems/
    ├── Invertibility.lean          ← det > 0, IsUnit det
    ├── ClosedForm.lean             ← explicit 2×2 inverse, uniqueness
    ├── CostToNormalEquation.lean   ← ∂cost/∂t = 0 ↔ normal equation
    ├── PropagationRadius.lean      ← k-pass locality / support growth bounds
    ├── Conditioning.lean           ← eigenvalues, κ = 1 + q(α)/s
    ├── ContractionBounds.lean      ← relaxed updates, λ_max, and iteration budgets
    ├── NearBinary.lean             ← meanResidual correction around weighted means
    └── CompositingError.lean       ← |Δcompose| ≤ α|ΔF| + (1-α)|ΔB|
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
- **Normalized-Weight Means** — With `λ_j = w_j / W`, the existing weighted means admit the
  equivalent forms `foregroundMean = ∑ j, λ_j F_j` and `backgroundMean = ∑ j, λ_j B_j`, and
  the normalized weights sum to `1`.
- **Compositing Error** — `|compose α F B − compose α F' B'| ≤ |α|·|F−F'| + |1−α|·|B−B'|`;
  authored corollary with simplified weights when `0 ≤ α ≤ 1`.

**Stage 3 (Deductive Synthesis):**

- **Closed-Form Solution** — Explicit 2×2 inverse solves the normal equation (det ≠ 0
  proof); solution is unique; equals matrix-inverse form.
- **Near-Binary Mean-Residual Correction** — The closed-form foreground/background updates are
  exposed as weighted means plus a shared `meanResidual`; by uniqueness the same pair of
  correction formulas characterizes any normal-equation solution.
- **Cost–Normal-Equation Bridge** — Local cost expands as a quadratic in perturbation `t`;
  genuine `HasDerivAt` derivatives; `IsCostStationary ↔ SolvesNormalEquation`.
- **Propagation Radius Bounds** — fixed-level Jacobi and Blur-Fusion `k`-pass outputs depend
  only on the recursively expanded `k`-hop neighborhood induced by the builder locality law.
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

**Options:**

| Flag                   | Values        | Default     | Description                               |
| ---------------------- | ------------- | ----------- | ----------------------------------------- |
| `--mode`               | `reference`   | `reference` | Solver mode                               |
| `--levels`             | `auto` \| _N_ | `auto`      | Level count (`auto` = `⌈log₂(max(w,h))⌉`) |
| `--small-size`         | _N_           | `32`        | Threshold for small-level iteration count |
| `--n-small-iterations` | _N_           | `10`        | Iterations at small levels                |
| `--n-big-iterations`   | _N_           | `2`         | Iterations at large levels                |
| `--eps-r`              | _X_           | `0.00001`   | Regularization ε_r                        |
| `--omega`              | _X_           | `1.0`       | Neighbor weight ω                         |

## Testing

There is no separate test suite. Smoke executables serve as regression checks:

- `ffiLeanSmoke` — exercises the Lean FFI bindings (NativeGrayImage, refine, clamp, resize)
- `ffiCliSmoke` — end-to-end CLI invocation with synthetic images
- `ffiSmoke` — pure C++ unit tests for the FFI functions
- `ffiRunner` — command-line PGM-based refinement runner

```sh
lake build ffiLeanSmoke && .lake/build/bin/ffiLeanSmoke
lake build ffiCliSmoke && .lake/build/bin/ffiCliSmoke
lake build ffiSmoke && .lake/build/bin/ffi-smoke
```

## Project Structure

| Path                | Role                                                        |
| ------------------- | ----------------------------------------------------------- |
| `FastMLFE2/`        | Main Lean source modules                                    |
| `native/`           | C++ FFI implementation ([README](native/README.md))         |
| `docs/`             | Architecture and design documents ([index](docs/README.md)) |
| `lakefile.lean`     | Lake build configuration                                    |
| `lean-toolchain`    | Lean version pin                                            |
| `main.tex`          | Companion LaTeX paper source                                |
| `FFILeanSmoke.lean` | Lean-side FFI smoke test                                    |
| `FFICliSmoke.lean`  | CLI integration smoke test                                  |
| `FastMLFECli.lean`  | CLI executable entry point                                  |

## Dependencies

| Dependency                                                  | Version | Purpose                                       |
| ----------------------------------------------------------- | ------- | --------------------------------------------- |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | v4.28.0 | Linear algebra, analysis, real number library |
| [REPL](https://github.com/leanprover-community/repl)        | v4.28.0 | Interactive Lean REPL support                 |
| OpenCV 4                                                    | system  | Image I/O and resize (native FFI only)        |

## License

See repository for license information.
