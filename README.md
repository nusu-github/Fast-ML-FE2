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

### Two-Layer Architecture

| Layer      | Import root        | Purpose                                                                                            |
| ---------- | ------------------ | -------------------------------------------------------------------------------------------------- |
| **Theory** | `FastMLFE2.Theory` | Formal mathematics: local equation, compositing, canonical semantics, assumption bundles, theorems |
| **Legacy** | `FastMLFE2.Legacy` | Executable runtime: CLI, multilevel solver, native C++ FFI                                         |

`FastMLFE2.Theory` is the default library target and the primary surface.
See [docs/architecture.md](docs/architecture.md) for the full layered design.

## Module Map

```txt
FastMLFE2.lean                          ← umbrella (imports Theory only)
FastMLFE2/
├── Theory.lean                         ← theory umbrella import
│   ├── Core/
│   │   ├── LocalEquation.lean          ← local context, cost, normal matrix, RHS
│   │   └── LocalSemantics.lean         ← solution / stationarity relations
│   ├── Compositing/
│   │   └── OneChannel.lean             ← α·F + (1-α)·B semantics
│   ├── Canonical/
│   │   ├── LocalCommitments.lean       ← stencil, resize rule, iteration semantics
│   │   └── MultilevelSchedule.lean     ← level-size computation
│   ├── Approximation/
│   │   └── BlurFusion.lean             ← idealized PhotoRoom Blur-Fusion surrogate
│   ├── Assumptions/
│   │   └── Bundles.lean                ← CoreMathAssumptions, variant bundles
│   └── Theorems/
│       ├── Invertibility.lean          ← det > 0, IsUnit det
│       ├── ClosedForm.lean             ← explicit 2×2 inverse, uniqueness
│       ├── CostToNormalEquation.lean   ← ∂cost/∂t = 0 ↔ normal equation
│       ├── PropagationRadius.lean      ← k-pass locality / support growth bounds
│       ├── Conditioning.lean           ← eigenvalues, κ = 1 + q(α)/s
│       └── CompositingError.lean       ← |Δcompose| ≤ α|ΔF| + (1-α)|ΔB|
├── Legacy.lean                         ← legacy umbrella (Runtime + CLI)
├── Runtime.lean                        ← runtime umbrella
│   ├── Runtime/Config.lean             ← ExecutionConfig, level scheduling
│   ├── Runtime/CliArgs.lean            ← CLI argument parsing
│   └── Runtime/Solver.lean             ← multilevel solver orchestration
├── CLI.lean                            ← CLI entry point
└── NativeFFI.lean                      ← opaque FFI bindings to C++

native/                                 ← C++ FFI sources (see native/README.md)
├── fastmlfe2_ffi.h
├── fastmlfe2_ffi.cpp
├── lean_fastmlfe2_ffi.cpp
├── smoke.cpp
└── runner.cpp
```

## Proved Theorems

The theory layer currently contains the following machine-checked results, mapped to the
pipeline stages:

For a more exhaustive module-by-module inventory, including the conditions under which each
result is proved, see [docs/THEOREMS.md](docs/THEOREMS.md).

**Stage 1 (Formal Specification):**

- Local cost function, 2×2 normal matrix, and RHS vector (`Theory.Core.LocalEquation`)
- Solution / stationarity relations (`Theory.Core.LocalSemantics`)
- Canonical commitments: 4-connected stencil, nearest-neighbor resize, deterministic
  simultaneous update (`Theory.Canonical`)
- Idealized Blur-Fusion approximation semantics (`Theory.Approximation.BlurFusion`)

**Stage 2 (Design-Space Exploration):**

- **Invertibility** — ε_r > 0 ⇒ neighbor weights positive; `totalWeight > 0`; normal
  matrix determinant positive and a unit.
- **Local Conditioning** — Normal matrix decomposes as `s·I + u·uᵀ` (rank-1 update);
  exact eigenvalues `s` and `s + q(α)` where `q(α) = α² + (1−α)²`; condition number
  `κ = 1 + q(α)/s` with bounds `1 + 1/(2s) ≤ κ ≤ 1 + 1/s`.
- **Compositing Error** — `|compose α F B − compose α F' B'| ≤ |α|·|F−F'| + |1−α|·|B−B'|`;
  authored corollary with simplified weights when `0 ≤ α ≤ 1`.

**Stage 3 (Deductive Synthesis):**

- **Closed-Form Solution** — Explicit 2×2 inverse solves the normal equation (det ≠ 0
  proof); solution is unique; equals matrix-inverse form.
- **Cost–Normal-Equation Bridge** — Local cost expands as a quadratic in perturbation `t`;
  genuine `HasDerivAt` derivatives; `IsCostStationary ↔ SolvesNormalEquation`.
- **Propagation Radius Bounds** — fixed-level Jacobi and Blur-Fusion `k`-pass outputs depend
  only on the recursively expanded `k`-hop neighborhood induced by the builder locality law.

## Prerequisites

- **Lean 4** — version specified in `lean-toolchain` (currently `v4.28.0`)
- **Mathlib** — fetched automatically by Lake (`v4.28.0`)
- **OpenCV 4** — headers and libraries via `pkg-config opencv4` (required for native FFI)
- **g++** with C++17 support

On Ubuntu/Debian:

```sh
sudo apt install libopencv-dev pkg-config g++
```

## Build

```sh
# Build the default library (Theory layer)
lake build

# Build the CLI executable
lake build fastmlfeCli

# Build smoke-test binaries
lake build ffiLeanSmoke ffiCliSmoke ffiSmoke ffiRunner

# Type-check a single file
lake env lean FastMLFE2/CLI.lean
```

## CLI Usage

```sh
.lake/build/bin/fastmlfeCli [options] image.png alpha.png out_fg.png out_bg.png
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
