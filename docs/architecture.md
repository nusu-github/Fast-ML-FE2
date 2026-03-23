# Architecture

This document describes the layered architecture of the Fast-ML-FE2 formalization project.

## Design Philosophy

The project formalizes Germer et al.'s Fast Multi-Level Foreground Estimation on Lean 4's
Dependent Type Theory, performing **proof-directed optimal implementation derivation** through
three stages:

### Stage 1 — Formal Specification

The algorithm's mathematical skeleton — cost function $\mathcal{L}_{\text{local}}(g_i^c)$,
normal equation $g_i^c = (U_i U_i^T + R^T V_i R)^{-1}(I_i^c U_i + R^T V_i h_i^c)$, and
multilevel pyramid recursion — is expressed as **denotational semantics** in Lean over
Mathlib's `ℝ`. Hardware and algorithmic constraints (FP precision, memory bandwidth, SIMD
width, warp size, neighborhood stencil, etc.) are injected as **parameterized axiom bundles**
— Lean `class` / `structure` typeclasses — forming a switchable **parametric theory**.

### Stage 2 — Formal Design-Space Exploration

For each axiom instantiation, **conditional equational theorems** are stated and proved or
disproved in Lean:

- **Binary α** ($\alpha_i \in \{0,1\}$) ⇒ the 2×2 inverse degenerates to diagonal form; F
  and B admit separable solutions (complexity reduction).
- **Channel independence** ⇒ the matrix $(U_i U_i^T + R^T V_i R)$ can be precomputed once
  and reused across RGB (formally guaranteed, not just claimed).
- **ε_r > 0** ⇒ positive definiteness of the normal matrix; existence of inverse.

This constitutes **exhaustive verification over the assumption lattice**.

### Stage 3 — Deductive Synthesis via Stepwise Refinement

Proved equalities serve as **rewrite rules** for equational reasoning from the abstract spec
toward computationally efficient forms:

- **Closed-form inverse**: rewrite to the 2×2 analytic formula
  $\frac{1}{ad-bc}\begin{bmatrix}d & -b \\ -c & a\end{bmatrix}$ with a det ≠ 0 proof.
- **Loop fusion**: prove semantic equivalence of fused neighbor-scan + matrix accumulation.
- **Data parallelism**: formally prove per-pixel local-solution independence (Jacobi
  iteration) ⇒ GPU parallelization correctness.

Each transformation is a **certified refinement** following the **Correct-by-Construction**
principle.

## Layer Diagram

```txt
┌─────────────────────────────────────────────────────┐
│  Theory Layer (FastMLFE2.Theory)                    │
│  ┌────────────────────────────────────────────────┐ │
│  │  Theorems                                      │ │
│  │  Invertibility · ClosedForm · CostBridge       │ │
│  │  Conditioning · CompositingError · Jacobi      │ │
│  │  Locality · CanonicalBuilder · Grid*           │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Assumptions                                   │ │
│  │  CoreMathAssumptions · GridMathAssumptions     │ │
│  │  Variant/Channel bundles                       │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Level                                         │ │
│  │  Jacobi · Locality                             │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Canonical Semantics                           │ │
│  │  Builder · Grid · GridContext                  │ │
│  │  LocalCommitments · MultilevelSchedule         │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Compositing                                   │ │
│  │  OneChannel: α·F + (1-α)·B                     │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Core                                          │ │
│  │  LocalEquation · LocalSemantics                │ │
│  └────────────────────────────────────────────────┘ │
├─────────────────────────────────────────────────────┤
│  Legacy Layer (FastMLFE2.Legacy)                    │
│  ┌────────────────────────────────────────────────┐ │
│  │  CLI · Runtime (Config, CliArgs, Solver)       │ │
│  │  NativeFFI · C++ FFI (native/)                 │ │
│  └────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────┘
```

## Theory Layer

### Core (`FastMLFE2.Theory.Core`)

The mathematical foundation. Defines the raw local optimization problem for a single pixel
without any algorithmic or backend commitments.

- **LocalEquation** — `LocalContext` structure carrying alpha, image value, neighbor
  values, and regularization parameters. Defines the local cost function, normal matrix
  (2×2), and right-hand side vector. All definitions are over `ℝ` using Mathlib.
- **LocalSemantics** — `SolvesNormalEquation`, `IsLocalSolution`, and `IsCostStationary`
  relations. These are the denotational semantics that theorems target.

### Compositing (`FastMLFE2.Theory.Compositing`)

- **OneChannel** — `compose α F B = α·F + (1-α)·B`. Provides simp lemmas for boundary
  cases (`α = 0`, `α = 1`) and algebraic difference identities.

### Canonical Semantics (`FastMLFE2.Theory.Canonical`)

Fixes the algorithmic choices where the Germer paper and PyMatting reference implementation
agree.

- **Builder** — dependent-neighbor canonical builder data. Connects authored pixel data to
  the abstract `LocalContextBuilder`/`Neighborhood` layer.
- **Grid** — faithful `Fin h × Fin w` geometry for boundary-aware four-connected
  neighborhoods. Each pixel gets its own valid-direction subtype, so missing boundary
  directions are omitted rather than padded.
- **GridContext** — thin aliases from `GridPixelData` into the canonical local-context
  surface. Provides `GridPixelData.localCtx` as the authored one-pixel context on faithful
  grid geometry.
- **LocalCommitments** — Enumerates shared commitments: four-connected neighborhood,
  nearest-neighbor resize, projection inside iteration, deterministic simultaneous update.
- **MultilevelSchedule** — `levelSizes` computing the coarse-to-fine pyramid using
  `size^(level/levelCount)` interpolation.

### Assumptions (`FastMLFE2.Theory.Assumptions`)

Explicit assumption bundles that parameterize what varies across backends and usage scenarios.

- **Bundles** — `CoreMathAssumptions` typeclass (ε_r > 0, ω ≥ 0, alpha bounded, neighbors
  nonempty). Additional structures for channel mode, backend schedule variant
  (canonical/CPU-async/GPU-Jacobi), initialization policy, projection, and hardware.
- **Grid** — `GridMathAssumptions` bundle for authored grid data. Carries the global
  hypotheses needed to recover `CoreMathAssumptions` pointwise on faithful grid contexts.

### Level (`FastMLFE2.Theory.Level`)

Abstract one-level update semantics above the local solver kernel.

- **Jacobi** — simultaneous pointwise update on a finite pixel index set. Defines
  `PixelState`, `LocalContextBuilder`, `jacobiUpdateAt`, and `jacobiStep`.
- **Locality** — abstract neighborhood-sensitive dependence laws for builders and Jacobi
  updates. States when a pointwise update depends only on a designated neighborhood of the
  old state.

### Theorems (`FastMLFE2.Theory.Theorems`)

Machine-checked results under explicit assumptions.

- **Invertibility** — Neighbor weight positivity propagated to `totalWeight > 0`, then
  `det(A) > 0` and `IsUnit det(A)`.
- **ClosedForm** — Explicit 2×2 inverse formula; proved to solve the normal equation;
  uniqueness of solution; equivalence with matrix-inverse form.
- **CostToNormalEquation** — Quadratic expansion of line-cost in perturbation parameter;
  genuine `HasDerivAt` derivatives; the key equivalence
  `IsCostStationary ↔ SolvesNormalEquation`.
- **Conditioning** — Rank-1 decomposition `A = s·I + u·uᵀ`; exact eigenvalues `s` and
  `s + q(α)` where `q(α) = α² + (1−α)²`; condition number `κ = 1 + q(α)/s` with tight
  bounds.
- **CompositingError** — Triangle-inequality bound on compositing difference in terms of
  component errors; tighter authored form when `0 ≤ α ≤ 1`.
- **Jacobi** — pointwise lifting theorems showing each simultaneous Jacobi-updated pixel is
  a closed-form local solution, solves the local normal equation, and is cost-stationary.
- **Locality** — proves that builder locality lifts to `jacobiUpdateAt` and `jacobiStep`.
- **CanonicalBuilder** — field-correctness theorems for authored canonical builders and the
  proof that they satisfy the abstract builder-locality law.
- **Grid** — faithful two-dimensional four-neighbor geometry; proves the canonical grid
  neighborhood agrees with the authored builder neighborhood, plus the exact `4/3/2`
  valid-direction counts for interior, edge, and corner pixels under the stated hypotheses.
- **GridNonempty** — constructive witness theorems supplying `Nonempty (ValidDir p)` for
  interior, edge, and corner cases.
- **GridAssumptions** — bridge from `GridMathAssumptions` plus local neighbor nonemptiness
  to `CoreMathAssumptions` on authored grid contexts.
- **GridLocal** — thin wrapper theorems exposing existing local closed-form theorems on
  `GridPixelData.localCtx`.

## Legacy Layer

### Runtime (`FastMLFE2.Runtime`)

Executable multilevel solver aligned with the PyMatting reference implementation.

- **Config** — `ExecutionConfig` record and level-size scheduling functions.
- **CliArgs** — Argument parsing for the CLI executable.
- **Solver** — `runMultilevelForegroundEstimation`: mean-color initialization, coarse-to-fine
  loop with nearest-neighbor resize and iterative refinement via FFI.

### CLI (`FastMLFE2.CLI`)

Thin entry point wrapping `Runtime.parseCliInvocation` and `Runtime.runCliInvocation`.

### NativeFFI (`FastMLFE2.NativeFFI`)

Opaque Lean bindings to the C++ FFI layer. `NativeGrayImage` is an opaque type backed by a
C++ float buffer. `NativeRgbImage` is a Lean structure of three `NativeGrayImage` channels.

### C++ FFI (`native/`)

Reference C++ implementation. See [native/README.md](../native/README.md).

## Import Graph

```txt
FastMLFE2  (default target)
  └── Theory
        ├── Core.LocalEquation
        ├── Core.LocalSemantics ──► Core.LocalEquation
        ├── Compositing.OneChannel
        ├── Level.Jacobi
        ├── Level.Locality
        ├── Canonical.Builder
        ├── Canonical.Grid
        ├── Canonical.GridContext
        ├── Canonical.LocalCommitments
        ├── Canonical.MultilevelSchedule
        ├── Assumptions.Bundles ──► Core.LocalEquation
        ├── Assumptions.Grid ──► Canonical.Grid, Assumptions.Bundles
        └── Theorems.*  ──► Core.*, Compositing.*, Level.*, Canonical.*, Assumptions.*

FastMLFE2.Legacy
  ├── Runtime  (Config, CliArgs, Solver ──► NativeFFI)
  └── CLI ──► Runtime
```

## Design Rationale

1. **Shallow embedding for math.** The local equation lives directly in Mathlib's `ℝ` and
   `Matrix` types. This gives immediate access to `ring`, `field_simp`, `linarith`, and
   Mathlib's linear algebra library.

2. **Explicit assumptions.** Every theorem states its hypotheses through `CoreMathAssumptions`
   or similar bundles. No global axioms beyond Lean's core and Mathlib's.

3. **Clean theory/runtime separation.** The default `lake build` produces only the theory
   library. The runtime requires native FFI and OpenCV — a strictly optional dependency.

4. **Canonical then variant.** The canonical layer records what the paper and PyMatting agree
   on. Backend-specific divergences (CPU async in-place, GPU Jacobi) are modeled as separate
   `BackendScheduleVariant` values with planned relational theorems.

5. **Refoundation, not wrapping.** The theory was built from scratch around the mathematics,
   not by wrapping the C++ implementation in Lean types. The runtime is kept for comparison
   but does not define correctness.
