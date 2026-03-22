# FastMLFE2 Theory Refoundation Design

Date: 2026-03-22
Status: Approved for planning
Project: FastMLFE2

## Purpose

Rebuild the project around a formal mathematical theory of Fast Multi-Level Foreground Estimation rather than around a native runtime or a proof-after-the-fact executable reference implementation.

The new project goal is:

1. Formalize the mathematical core of Fast Multi-Level Foreground Estimation in Lean 4.
2. Express assumptions as explicit parameter bundles that can be instantiated and varied.
3. Prove conditional theorems over the resulting assumption lattice.
4. Derive efficient CPU and GPU implementation forms by certified refinement from the mathematical specification.

The project is therefore a proof-directed design-space exploration system for the algorithm, not a verification wrapper around an existing implementation.

## Problem Statement

The current repository mixes:

- local algebraic proofs,
- abstract specification fragments,
- multilevel skeletons,
- runtime configuration,
- Lean FFI,
- C++ kernels,
- CLI entrypoints,
- smoke tests tied to one executable behavior.

That shape is not aligned with the intended research objective. It centers executable behavior and treats Lean as a justification layer. The desired direction is the opposite: Lean should define the mathematical object, the space of assumptions, and the allowed correctness-preserving transformations, while executable implementations become optional backends derived later.

## Design Principles

1. Theory first.
   The mathematical local solver is the primary object. Multilevel structure and implementation detail are secondary layers.

2. Separate correctness from efficiency.
   Mathematical truth, algorithmic choice, and hardware advantage must be represented by different definitions and different theorem families.

3. Make assumptions explicit.
   Every meaningful precondition must be represented as a Lean structure or type class, not as an undocumented convention.

4. Prefer shallow mathematics before deep optimization IR.
   The first successful formalization target is a shallow denotational theory of the local equation. Deep embedding comes later as a refinement layer.

5. Clean break over compatibility.
   Existing runtime, native, and CLI layers are not architectural anchors. They may be deleted if they obstruct the theory-first structure.

6. Refinement must be certified.
   Every step from abstract mathematics to implementation-oriented form must be justified by an explicit theorem.

## Scope

### In Scope

- A formal shallow embedding of the single-pixel local foreground/background equation.
- Explicit assumption bundles for mathematics, algorithmic strategy, and hardware model parameters.
- Conditional theorems such as invertibility, degeneracy, channel reuse, and closed-form reduction.
- A fixed-level Jacobi update semantics built from the local solver.
- A deep refinement IR for certified algebraic and implementation-oriented rewrites.
- A migration path that removes current runtime-centric structure in favor of a theory-centric structure.

### Out of Scope for the Initial Rebuild

- Preserving the current CLI surface.
- Preserving the current FFI or native C++ layout.
- Immediate parity with the existing PyMatting CPU or GPU implementation.
- Full multilevel semantics in the first proof layer.
- Immediate code generation for all backends.

## Core Formalization Strategy

### Primary Object

The primary object is the single-pixel local equation for one color channel. The base semantic object is the local unknown:

- foreground value at pixel `i`,
- background value at pixel `i`.

The first formal theory covers:

- local cost function,
- normal equation,
- conditions for invertibility,
- closed-form analytic solution,
- algebraic simplifications under explicit assumptions.

### Embedding Strategy

The project uses a hybrid strategy.

- The mathematical core is formalized as a shallow embedding using ordinary Lean functions, predicates, matrices, and real-valued expressions.
- The optimization and implementation-derivation layer is formalized as a deep embedding using an explicit IR and denotation function.

This split keeps early mathematical progress fast while still supporting proof-directed synthesis later.

### First Main Theorem

The first main theorem family is local-system well-posedness and closed-form solvability:

- the local coefficient matrix is invertible under explicit assumptions,
- the closed-form 2x2 inverse is valid,
- the resulting expression is equal to the abstract local solution,
- special assumption bundles induce further simplifications.

The first layer does not attempt to formalize the full multilevel algorithm.

## Architecture

### Layer 1: Theory Core

This layer defines the local mathematical object and its denotational semantics.

Planned modules:

- `FastMLFE2/Theory/Core/LocalEquation.lean`
- `FastMLFE2/Theory/Core/LocalSemantics.lean`

Responsibilities:

- define local state and local parameters,
- define the local cost function,
- define the normal matrix and right-hand side,
- define the denotational solution target,
- state the exact mathematical semantics independent of execution strategy.

This layer must not depend on runtime code, native code, IO, CLI logic, or hardware lowering logic.

### Layer 2: Assumption Bundles

This layer defines explicit parameterized assumptions.

Planned modules:

- `FastMLFE2/Theory/Assumptions/Bundles.lean`
- `FastMLFE2/Theory/Assumptions/Instances/*.lean`

Representative bundles:

- `RegularizationAssumptions`
- `AlphaAssumptions`
- `NeighborhoodAssumptions`
- `ChannelAssumptions`
- `AlgorithmicAssumptions`
- `HardwareAssumptions`

Responsibilities:

- make theorem preconditions explicit,
- support multiple assumption instantiations,
- define the assumption lattice explored by later theorems.

The key separation is:

- mathematical assumptions describe what is true of the model,
- algorithmic assumptions describe which solver strategy is chosen,
- hardware assumptions describe performance-relevant constraints but do not change mathematical denotation.

### Layer 3: Conditional Theorems

This layer proves conditional algebraic facts over the assumption bundles.

Planned modules:

- `FastMLFE2/Theory/Theorems/Invertibility.lean`
- `FastMLFE2/Theory/Theorems/ClosedForm.lean`
- `FastMLFE2/Theory/Theorems/Degeneracy.lean`
- `FastMLFE2/Theory/Theorems/ChannelReuse.lean`
- `FastMLFE2/Theory/Theorems/Regularization.lean`

Representative theorem families:

- `epsilon_r > 0` implies determinant positivity or equivalent invertibility condition,
- binary alpha assumptions imply matrix degeneracy into a simpler form,
- channel independence implies matrix reuse across RGB channels,
- the analytic 2x2 inverse is extensionally equal to the abstract inverse-based solution.

This layer is the main site for formal design-space exploration.

### Layer 4: Fixed-Level Jacobi Semantics

This layer lifts the local solution into a whole-image single-level update law.

Planned modules:

- `FastMLFE2/Theory/Level/Jacobi.lean`
- `FastMLFE2/Theory/Level/Parallelism.lean`

Responsibilities:

- define a full-image simultaneous update operator,
- prove that each pixel update depends only on old state,
- prove order independence of the simultaneous form,
- justify map-style and data-parallel evaluation.

This layer is where GPU-style parallel justification first appears.

### Layer 5: Refinement IR

This layer introduces the deep embedding used for proof-directed derivation.

Planned modules:

- `FastMLFE2/Refinement/IR.lean`
- `FastMLFE2/Refinement/Denotation.lean`
- `FastMLFE2/Refinement/Rewrite.lean`
- `FastMLFE2/Refinement/CostModel.lean`
- `FastMLFE2/Refinement/Backends/*.lean`

Responsibilities:

- define optimization-oriented expression trees or kernel IR,
- define denotation into the shallow theory,
- prove rewrite soundness,
- attach hardware-sensitive cost models,
- support backend-specific lowering once correctness-preserving rewrites are available.

## Theorem Pipeline

The theorem pipeline is fixed in the following order.

### 1. Well-Posedness Theorems

These establish that the local problem is mathematically meaningful.

Examples:

- determinant nonzero conditions,
- invertibility,
- positive definiteness or sufficient substitutes,
- existence and uniqueness of the local solution under stated assumptions.

### 2. Algebraic Equivalence Theorems

These expose the first optimization opportunities.

Examples:

- inverse-based local solution equals analytic 2x2 closed form,
- channel-independent coefficient matrix reuse,
- binary alpha simplification,
- simplification under special neighborhood or regularization assumptions.

### 3. Lifting Theorems

These move from the local equation to a full-image fixed-level semantics.

Examples:

- the local solver induces a Jacobi update operator,
- each output pixel depends only on the old state,
- the update is compatible with data-parallel evaluation,
- per-pixel computations can be re-expressed as a map over pixels.

### 4. Refinement Theorems

These justify implementation-oriented rewrites.

Examples:

- 2x2 inverse expansion rewrite,
- loop fusion of neighbor traversal and accumulator construction,
- explicit coefficient precomputation,
- extraction of data-parallel kernels,
- backend-oriented lowerings that preserve denotation.

## Assumption Taxonomy

The project standardizes the assumption taxonomy to avoid category mistakes.

### Mathematical Assumptions

Examples:

- `epsilon_r > 0`,
- alpha is in `[0, 1]`,
- weight nonnegativity,
- binary alpha,
- channel independence.

These affect truth of mathematical statements.

### Algorithmic Assumptions

Examples:

- four-connected or eight-connected neighborhood,
- Jacobi vs other update style,
- resize rule,
- initialization rule,
- level schedule.

These affect the chosen solver architecture, not the local mathematical truth.

### Hardware Assumptions

Examples:

- floating-point model,
- vector width,
- warp size,
- memory constraints,
- coalescing assumptions,
- shared-memory budgets.

These affect which refinement is favorable. They do not change the denotational semantics of the mathematical theory.

## Semantic Boundary

Two semantics are defined and kept distinct.

### Denotational Semantics

This semantics assigns mathematical meaning to:

- local equations,
- local solutions,
- full-image single-level Jacobi updates,
- later multilevel compositions.

This semantics is the reference notion of correctness.

### Refinement Semantics

This semantics connects deep IR objects to denotational meanings.

A rewrite or lowering is valid only if its denotation is provably equal to the source denotation. Cost-model preference is handled separately and never substitutes for semantic equality.

## Migration Strategy

The repository moves by clean break, not by compatibility preservation.

### Delete or Isolate

The following components are no longer architectural anchors:

- `FastMLFE2/Runtime/*`
- `FastMLFE2/NativeFFI.lean`
- `FastMLFE2/CLI.lean`
- `FastMLFECli.lean`
- `native/*`
- smoke executables tied only to runtime behavior

These may be deleted outright or temporarily isolated as comparison backends. They must not define the core architecture.

### Salvage Carefully

Existing proof fragments may be selectively migrated only if they serve the new theory-first architecture. In particular:

- useful local algebra lemmas may be moved into `Theory/Core` or `Theory/Theorems`,
- any theorem whose meaning depends on the old runtime path rather than on the mathematical theory is not preserved by default.

### New Namespace Direction

The new central namespace is theory-oriented:

- `FastMLFE2.Theory.*`
- `FastMLFE2.Refinement.*`

Runtime- or backend-oriented namespaces become optional leaves rather than the trunk of the project.

## Error Handling and Failure Modes

The theory layer must model explicit failure boundaries.

At the mathematical level:

- undefined inverse conditions must be represented as theorem preconditions, not hidden by partial definitions,
- special cases such as binary alpha or zero regularization must be represented as distinct assumption regimes rather than as ad hoc branches.

At the refinement layer:

- rewrites must declare the exact assumptions they require,
- backend lowering must fail at the proof level if required assumptions are absent,
- performance claims must be conditional on hardware bundles and cost-model hypotheses.

## Verification Strategy

Verification is staged.

### Theory Verification

- Lean theorem checking for all core results,
- axiom minimization where possible,
- explicit theorem dependencies on assumption bundles.

### Refinement Verification

- proof that each rewrite preserves denotation,
- proof that each lifted fixed-level operator matches its shallow specification.

### Backend Validation

Executable backends, if retained, are validated against derived theory artifacts after the theory is established. Backend agreement tests are not substitutes for core theory proofs.

## Testing Strategy

The rebuilt project will distinguish proof artifacts from validation artifacts.

Proof artifacts:

- theorem files in `Theory` and `Refinement`.

Validation artifacts:

- optional numerical comparison suites against Python or native backends,
- optional performance experiments under instantiated hardware bundles,
- backend conformance tests after refinement theorems exist.

The project will not present backend smoke tests as evidence of mathematical correctness.

## Non-Goals

The initial rebuild does not attempt to:

- prove the full multilevel algorithm before the local theory is stable,
- preserve the current CLI and C++ architecture,
- force immediate parity with PyMatting,
- encode all hardware models from the start,
- solve code generation before rewrite soundness is in place.

## Success Criteria

The refoundation is successful when all of the following hold:

1. The single-pixel local equation has a standalone denotational formalization.
2. Assumptions are explicit bundles rather than hidden conventions.
3. Invertibility and closed-form theorems are reusable over the assumption lattice.
4. A whole-image fixed-level Jacobi operator is lifted from the local solver.
5. A deep refinement IR exists with denotation and sound rewrite theorems.
6. Runtime or backend code is clearly downstream of theory rather than upstream of it.

## Recommended Next Planning Unit

The first implementation plan should cover only the initial theory kernel:

- create the new theory-oriented module tree,
- formalize the single-pixel local equation,
- define the initial assumption bundles,
- prove the first invertibility and closed-form theorem family,
- remove or isolate legacy runtime-centric modules so they do not shape the new architecture.

This scope is intentionally narrower than full multilevel formalization. It is the minimal unit that establishes the new architectural center of gravity.
