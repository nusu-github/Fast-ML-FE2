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
│  Theory Layer (FastMLFE2)                    │
│  ┌────────────────────────────────────────────────┐ │
│  │  Theorems                                      │ │
│  │  Invertibility · ClosedForm* · CostBridge      │ │
│  │  Conditioning · BinaryAlpha* · ChannelReuse    │ │
│  │  NormalizedWeights · ClampLocal                │ │
│  │  JacobiContraction · ClampPlacement*           │ │
│  │  BlurFusion* · BleedThrough · MeanResidual*    │ │
│  │  ContractionBounds · NearBinary*               │ │
│  │  PropagationRadius · SpatialDecay              │ │
│  │  CompositingError · Jacobi · Locality          │ │
│  │  IterationInvariance · CanonicalBuilder        │ │
│  │  Grid* · InteriorKernel · FixedPrecision*      │ │
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
│  │  InteriorKernel · ClampPlacement               │ │
│  │  LocalCommitments · MultilevelSchedule         │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Evaluation                                    │ │
│  │  ForegroundMetrics · AdversarialFamilies       │ │
│  │  ContinuousGrad · StepEdgeFamilies             │ │
│  │  DiscreteGrad · DiscreteGradFamilies           │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Approximation                                 │ │
│  │  BlurFusion surrogate semantics                │ │
│  ├────────────────────────────────────────────────┤ │
│  │  FixedPrecision                                │ │
│  │  Format · Coefficients · LocalSolver           │ │
│  │  Jacobi · Cost · Multilevel                    │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Compositing                                   │ │
│  │  OneChannel: α·F + (1-α)·B                     │ │
│  ├────────────────────────────────────────────────┤ │
│  │  Core                                          │ │
│  │  LocalEquation · LocalSemantics                │ │
│  └────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────┘
```

## Theory Layer

### Core (`FastMLFE2.Core`)

The mathematical foundation. Defines the raw local optimization problem for a single pixel
without any algorithmic or backend commitments.

- **LocalEquation** — `LocalContext` structure carrying alpha, image value, neighbor
  values, and regularization parameters. Defines the local cost function, normal matrix
  (2×2), and right-hand side vector. All definitions are over `ℝ` using Mathlib.
- **LocalSemantics** — `SolvesNormalEquation`, `IsLocalSolution`, and `IsCostStationary`
  relations. These are the denotational semantics that theorems target.

### Compositing (`FastMLFE2.Compositing`)

- **OneChannel** — `compose α F B = α·F + (1-α)·B`. Provides simp lemmas for boundary
  cases (`α = 0`, `α = 1`) and algebraic difference identities.

### Canonical Semantics (`FastMLFE2.Canonical`)

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
- **InteriorKernel** — Interior-pixel specialized surface. `interiorToValidDir` injects
  all four `Direction4` directions into `ValidDir p` for interior pixels. `interiorLocalCtx`
  and `interiorClosedFormSolution` expose the local context and closed-form solver without
  subtype plumbing at call sites.
- **ClampPlacement** — Projection-policy variants for `CanonicalPixelData`: `rawStep`
  (no projection), `insideClampedStep` (clamp after each step), `endClampedIterate` (clamp
  only at the end of `k` steps). Includes concrete counterexample data showing the three
  policies can disagree.
- **LocalCommitments** — Enumerates shared commitments: four-connected neighborhood,
  nearest-neighbor resize, projection inside iteration, deterministic simultaneous update.
- **MultilevelSchedule** — `levelSizes` computing the coarse-to-fine pyramid using
  `size^(level/levelCount)` interpolation.

### Approximation (`FastMLFE2.Approximation`)

Explicit surrogate semantics for approximation families derived from, but not identified with,
the canonical Germer objective.

- **BlurFusion** — Idealized real-valued PhotoRoom-style Blur-Fusion semantics: masked weighted
  means, separated surrogate costs, the sequential foreground correction, and induced
  builder-level `x1`/`x2`/`xk` update maps.

### Evaluation (`FastMLFE2.Evaluation`)

Metric semantics and adversarial test families used to stress foreground-estimation outputs.

- **ForegroundMetrics** — finite-grid RGB image model, translucent support, paper-weighted
  `SAD` / `MSE`, and an abstract `GRAD` operator interface.
- **AdversarialFamilies** — near-opaque alpha fields together with saturating black/white
  foreground pairs that witness the `SAD` / `MSE` supremum family.
- **ContinuousGrad** — continuous-window Gaussian `GRAD` semantics specialized to vertical
  step edges on `ℝ × ℝ`.
- **StepEdgeFamilies** — canonical continuous black/white edge, flat reference, and shifted-edge
  families aligned with the `ContinuousGrad` theorem layer.
- **DiscreteGrad** — exact discrete `GRAD` semantics matching the Python evaluation kernel at
  default `sigma = 1.4`, including sampled kernels, reflect padding, and separable correlation.
- **DiscreteGradFamilies** — discrete witness families for step-pattern stress tests that mirror
  the Python-side synthetic generators.

### Fixed Precision (`FastMLFE2.FixedPrecision`)

Models fixed-width integer/floating-point arithmetic for the entire pipeline, from coefficient
computation through multilevel scheduling.

- **Format** — `FixedFormat` structure (word width, accumulator width, scale, rounding mode);
  `Storage`, `Accumulator`, `Coefficient` as `BitVec` aliases; `decodeStorage`/`decodeAccumulator`
  bridging bit-vectors to `ℝ`.
- **Coefficients** — `ReciprocalTableSpec` defining weight/gain reciprocal domains;
  `coefficientQuantizationBudget`; table-lookup reciprocals.
- **LocalSolver** — `FixedLocalContext` carrying per-pixel fixed-point data; `NoWrapLocalStep`
  and `LocalRangeCert`/`LocalSafetyCert` predicates; `fixedMeanResidualStep` and
  `fullyFixedMeanResidualStep` update functions.
- **Jacobi** — `FixedLocalContextBuilder`, `fixedJacobiStep`/`fullyFixedJacobiStep`, and
  their `n`-fold iterates.
- **Cost** — `WeightedCostModel` with per-operation weights; `localStepCost`,
  `referenceLocalStepCost`, and per-iteration/multilevel cost functions.
- **Multilevel** — `FixedGridState`, `FixedGridBuilder`, `FixedLevelSpec`; nearest-neighbor
  resize; red-black sweep ordering (`CheckerColor`); `multilevelCost`.

### Assumptions (`FastMLFE2.Assumptions`)

Explicit assumption bundles that parameterize what varies across backends and usage scenarios.

- **Bundles** — `CoreMathAssumptions` typeclass (ε_r > 0, ω ≥ 0, alpha bounded, neighbors
  nonempty). Additional structures for channel mode, backend schedule variant
  (canonical/CPU-async/GPU-Jacobi), initialization policy, projection, and hardware.
- **Grid** — `GridMathAssumptions` bundle for authored grid data. Carries the global
  hypotheses needed to recover `CoreMathAssumptions` pointwise on faithful grid contexts.

### Level (`FastMLFE2.Level`)

Abstract one-level update semantics above the local solver kernel.

- **Jacobi** — simultaneous pointwise update on a finite pixel index set. Defines
  `PixelState`, `LocalContextBuilder`, `jacobiUpdateAt`, and `jacobiStep`.
- **Locality** — abstract neighborhood-sensitive dependence laws for builders and Jacobi
  updates. States when a pointwise update depends only on a designated neighborhood of the
  old state.

### Theorems (`FastMLFE2.Theorems`)

Machine-checked results under explicit assumptions.

- **Invertibility** — Neighbor weight positivity propagated to `totalWeight > 0`, then
  `det(A) > 0` and `IsUnit det(A)`.
- **ClosedForm** — Explicit 2×2 inverse formula; proved to solve the normal equation;
  uniqueness of solution; equivalence with matrix-inverse form.
- **ClosedFormBox** — Conditional `[0,1]` membership of the closed-form solution from
  numerator bounds; `clamp01` acts as identity when bounds hold.
- **ClosedFormBoxInput** — `closedFormForegroundMeanAffine` mean-affine solution form;
  explicit counterexample showing the naive box-input `[0,1]` claim fails without extra
  hypotheses.
- **ClosedFormMeanResidual** — `meanResidualSolution` exposing the shared `meanResidual`
  correction; by uniqueness this characterizes any normal-equation solution.
- **NormalizedWeights** — `normalizedWeight j = w_j / W`; `foregroundMean` and
  `backgroundMean` as normalized-weight sums; normalized weights sum to `1`.
- **CostToNormalEquation** — Quadratic expansion of line-cost in perturbation parameter;
  genuine `HasDerivAt` derivatives; the key equivalence
  `IsCostStationary ↔ SolvesNormalEquation`.
- **Conditioning** — Rank-1 decomposition `A = s·I + u·uᵀ`; exact eigenvalues `s` and
  `s + q(α)` where `q(α) = α² + (1−α)²`; condition number `κ = 1 + q(α)/s` with tight
  bounds.
- **BinaryAlpha** — Normal matrix, RHS, and `closedFormDenom` specializations for `α = 0`
  and `α = 1`; diagonal degenerations of the 2×2 system.
- **BinaryAlphaCost** — `localCost` form and stationarity conditions for binary `α`.
- **ChannelReuse** — `SameWeightData` and `SameRhsData` predicates; proves normal matrix,
  `totalWeight`, `weightedMeanDenom`, and `closedFormDenom` equal across contexts sharing
  only α, ε_r, ω. Formally guarantees shared-coefficient reuse in multi-channel processing.
- **ClampLocal** — `clamp01Scalar` is a fixed point exactly on `[0,1]`; `clamp01` and
  `clamp01Scalar` are non-expanding under the infinity norm.
- **JacobiContraction** — Contraction theorems for the core Jacobi definitions
  (`Core.LocalContext.jacobiStep`, `jacobiDiagForeground/Background`, `jacobiCrossTerm`);
  spectral radius `ρ < 1` under `CoreMathAssumptions`; geometric error contraction.
- **ClampPlacement** — `rawStepGain < 1`; inside-clamped and end-clamped iterates have
  distinct fixed-point sets (explicit counterexample supplied by `ClampPlacementCounterexample`).
- **CompositingError** — Triangle-inequality bound on compositing difference in terms of
  component errors; tighter authored form when `0 ≤ α ≤ 1`.
- **MeanResidualBounds** — Boxed-input bound on `|meanResidual|` plus foreground/background
  correction estimates.
- **ResidualCompositeBounds** — Exact compositing error written as a scaled mean residual;
  finite-family infinity-norm corollary.
- **ContractionBounds** — Relaxed updates contract for `0 < λ < λ_max = 2/(1+q)`; scalar
  sign-flip counterexample shows the bound is sharp; early-termination threshold from
  `E₀ q^k ≤ η`.
- **NearBinary** — `meanResidual`-corrected closed-form solution around weighted means;
  `NearBinaryCounterexample` refutes the naive clamp-binary swap claim.
- **BleedThrough** — Component-wise Jacobi iterate error bound
  `|fg_k − fg*| ≤ jacobiOneStepGain × ρ^(k−1) × ‖x₀ − x*‖∞`.
- **BlurFusionGap** — Synthetic `blurStageTwoCtx` whose local cost equals the Blur-Fusion
  stage-two surrogate; exact joint minimizer vs sequential stage-two output gap quantified.
- **BlurFusionFixedPoint** — Counterexample showing the Blur-Fusion `x1` update is generally
  not a fixed point and differs from the canonical closed-form Jacobi step.
- **ForegroundMetrics** — finite-grid `SAD` / paper `MSE` upper bounds together with exact
  values on saturating black/white adversarial families and supremum-attainment lemmas.
- **ContinuousGrad** — positivity and symmetry facts for the continuous Gaussian kernel plus
  lower-bound theorems for vertical `GRAD` on binary edge-vs-flat and shifted-edge families.
- **DiscreteGrad** — positivity, normalization, and odd-symmetry facts for the exact Python
  discrete kernel, together with step-family witness coefficients and nontriviality certificates.
- **Jacobi** — pointwise lifting theorems showing each simultaneous Jacobi-updated pixel is
  a closed-form local solution, solves the local normal equation, and is cost-stationary.
- **Locality** — proves that builder locality lifts to `jacobiUpdateAt` and `jacobiStep`.
- **IterationInvariance** — In a `CanonicalPixelData` builder, `neighborWeight`, `totalWeight`,
  and `weightedMeanDenom` are independent of the current pixel state across `build` calls.
- **PropagationRadius** — lifts builder locality through repeated Jacobi / Blur-Fusion passes,
  yielding recursive `k`-hop support bounds for fixed-level propagation.
- **SpatialDecay** — abstract exponential radius-decay and fixed-exterior halo envelopes.
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
- **InteriorKernel** — equivalence between `ValidDir`-indexed and `Direction4`-indexed
  contexts for interior pixels; `interiorLocalCtx` matches `localCtx` up to the
  `validDirEquivDirection4` bijection; closed-form solution correctness on interior contexts.
- **QuantizationBounds** — grid quantization error `|q(x) − x| < 1/S`; geometric series
  helpers for accumulation analysis.
- **FixedPrecisionLocal** — `NoWrapLocalStep` ⇒ decoded fixed-point step equals quantized
  real step; decoded wrapped sums match unwrapped integer sums.
- **FixedPrecisionJacobi** — `LocalRangeCert` lifts no-wrap to `fixedJacobiUpdateAt`;
  `LocalSafetyCert` equivalence for `fullyFixedJacobiUpdateAt`.
- **FixedPrecisionCost** — Safety-cert decoded step equals reference; cost model
  nonnegativity for local step, Jacobi iteration, and multilevel pipeline; reciprocal-table
  cost saving.
- **FixedPrecisionMultilevel** — Same-size nearest-neighbor resize is identity; red-black
  sweep and Jacobi step share fixed-point sets; multilevel cost nonnegativity.
- **FixedPrecisionWraparound** — Explicit 4-bit counterexample: `7 + 7 = −2` in signed
  `BitVec 4`, showing accumulator overflow invalidates decoded results.

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
        ├── Canonical.GridContext ──► Canonical.Grid, Canonical.Builder
        ├── Canonical.InteriorKernel ──► Canonical.GridContext
        ├── Canonical.ClampPlacement ──► Canonical.Builder
        ├── Canonical.LocalCommitments
        ├── Canonical.MultilevelSchedule
        ├── Approximation.BlurFusion
        ├── FixedPrecision.Format ──► Core.LocalEquation
        ├── FixedPrecision.Coefficients ──► FixedPrecision.Format, Theorems.QuantizationBounds
        ├── FixedPrecision.LocalSolver ──► FixedPrecision.Format, FixedPrecision.Coefficients
        ├── FixedPrecision.Jacobi ──► FixedPrecision.LocalSolver
        ├── FixedPrecision.Cost ──► FixedPrecision.Jacobi
        ├── FixedPrecision.Multilevel ──► FixedPrecision.Cost, Canonical.MultilevelSchedule
        ├── Assumptions.Bundles ──► Core.LocalEquation
        ├── Assumptions.Grid ──► Canonical.Grid, Assumptions.Bundles
        └── Theorems.*  ──► Core.*, Compositing.*, Level.*, Canonical.*, FixedPrecision.*, Assumptions.*
```

## Design Rationale

1. **Shallow embedding for math.** The local equation lives directly in Mathlib's `ℝ` and
   `Matrix` types. This gives immediate access to `ring`, `field_simp`, `linarith`, and
   Mathlib's linear algebra library.

2. **Explicit assumptions.** Every theorem states its hypotheses through `CoreMathAssumptions`
   or similar bundles. No global axioms beyond Lean's core and Mathlib's.

3. **Canonical then variant.** The canonical layer records what the paper and PyMatting agree
   on. Backend-specific divergences (CPU async in-place, GPU Jacobi) are modeled as separate
   `BackendScheduleVariant` values with planned relational theorems.

4. **Refoundation, not wrapping.** The theory is built from scratch around the mathematics.
   Correctness is defined by the formal semantics, not by any external implementation.
