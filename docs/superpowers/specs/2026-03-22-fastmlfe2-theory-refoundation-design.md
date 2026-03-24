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
5. Use the paper together with the published PyMatting CPU and GPU implementations to fix algorithmic ambiguities wherever the authored artifacts agree.

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

At the same time, the published CPU and GPU reference implementations are not irrelevant. They resolve some ambiguities left by the paper and expose others as genuine semantic divergences. The new design must therefore distinguish:

- mathematical core shared by paper, CPU, and GPU,
- canonical authored semantics where paper and implementations agree,
- backend-specific semantics where CPU and GPU diverge,
- hypothesis and relational theorem layers that compare those variants.

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

7. Fix what is shared, parameterize only what is genuinely variable.
   If the paper and authored implementations agree, treat that agreement as part of the canonical semantics rather than as a free assumption knob.

## Scope

### In Scope

- A formal shallow embedding of the single-pixel local foreground/background equation.
- Extraction of a canonical Germer/PyMatting semantics from the paper and from the shared behavior of the authored CPU and GPU implementations.
- Explicit assumption bundles for mathematics, semantic variants, and hardware model parameters.
- Conditional theorems such as invertibility, degeneracy, channel reuse, and closed-form reduction.
- A canonical fixed-level update semantics built from the local solver.
- A variant and relational theorem layer for backend divergences such as CPU asynchronous in-place iteration, initialization policies, and projection placement.
- A deep refinement IR for certified algebraic and implementation-oriented rewrites.
- A migration path that removes current runtime-centric structure in favor of a theory-centric structure.

### Out of Scope for the Initial Rebuild

- Preserving the current CLI surface.
- Preserving the current FFI or native C++ layout.
- Immediate bitwise or backend-complete parity with the existing PyMatting CPU or GPU implementation.
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

The first formal theory does not treat backend scheduling, resize policy, or initialization as part of the local mathematical core.

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

In particular, determinant positivity under `epsilon_r > 0` is a core theorem, not a research hypothesis.

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

### Layer 2: Canonical Germer/PyMatting Semantics

This layer captures choices that are not part of the pure local mathematics but are effectively fixed by the authored artifacts where the paper is ambiguous.

Planned modules:

- `FastMLFE2/Theory/Canonical/LocalCommitments.lean`
- `FastMLFE2/Theory/Canonical/LevelSemantics.lean`
- `FastMLFE2/Theory/Canonical/MultilevelSchedule.lean`

Representative commitments:

- four-neighbor local stencil,
- nearest-neighbor resize,
- clamp inside the iteration,
- the published multilevel level schedule,
- a deterministic fixed-level semantics used as the canonical authored semantics.

Responsibilities:

- define what counts as the canonical Germer/PyMatting semantics,
- separate authored commitments from abstract mathematical truth,
- serve as the reference target for backend comparison theorems.

The canonical layer is not the same thing as the backend layer. It is the intended authored semantics distilled from the shared structure of paper, CPU, and GPU artifacts.

### Layer 3: Assumption Bundles

This layer defines explicit parameterized assumptions for items that remain genuinely variable.

Planned modules:

- `FastMLFE2/Theory/Assumptions/Bundles.lean`
- `FastMLFE2/Theory/Assumptions/Instances/*.lean`

Representative bundles:

- `CoreMathAssumptions`
- `AlphaAssumptions`
- `ChannelAssumptions`
- `VariantAssumptions`
- `BackendScheduleAssumptions`
- `InitializationAssumptions`
- `ProjectionAssumptions`
- `HardwareAssumptions`

Responsibilities:

- make theorem preconditions explicit,
- support multiple assumption instantiations,
- define the assumption lattice explored by later theorems.

The key separation is:

- mathematical assumptions describe what is true of the model,
- canonical commitments describe authored choices that are not intended to vary on the main theory path,
- variant assumptions describe deliberate semantic deviations from the canonical path,
- hardware assumptions describe performance-relevant constraints but do not change mathematical denotation.

### Layer 4: Conditional Theorems

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

### Layer 5: Backend and Variant Semantics

This layer records the authored backend-specific semantics and other deliberate variants that differ from the canonical layer.

Planned modules:

- `FastMLFE2/Theory/Backends/CPUAsync.lean`
- `FastMLFE2/Theory/Backends/GPUJacobi.lean`
- `FastMLFE2/Theory/Variants/Initialization.lean`
- `FastMLFE2/Theory/Variants/Projection.lean`

Responsibilities:

- define backend-specific semantics precisely,
- distinguish canonical deterministic semantics from authored asynchronous or nondeterministic variants,
- provide targets for relational theorems,
- isolate places where authored implementations disagree.

In this layer, the CPU implementation is treated as an asynchronous in-place variant rather than as the canonical semantics.

### Layer 6: Refinement IR

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

This is where the former H5-style statement lives.

### 2. Algebraic Equivalence Theorems

These expose the first optimization opportunities.

Examples:

- inverse-based local solution equals analytic 2x2 closed form,
- channel-independent coefficient matrix reuse,
- binary alpha simplification,
- simplification under special neighborhood or regularization assumptions.

### 3. Canonical Lifting Theorems

These move from the local equation to the canonical Germer/PyMatting fixed-level semantics.

Examples:

- the local solver induces the canonical fixed-level update operator,
- each output pixel depends only on the old state,
- the update is compatible with data-parallel evaluation,
- per-pixel computations can be re-expressed as a map over pixels.

### 4. Variant and Relational Theorems

These compare canonical semantics to backend-specific or deliberately varied semantics.

Examples:

- Jacobi versus asynchronous in-place iteration,
- sensitivity to initialization choices,
- projection-inside versus projection-outside iteration,
- schedule robustness under backend-specific execution orders.

This is where the former H1-H4-style statements belong.

### 5. Refinement Theorems

These justify implementation-oriented rewrites.

Examples:

- 2x2 inverse expansion rewrite,
- loop fusion of neighbor traversal and accumulator construction,
- explicit coefficient precomputation,
- extraction of data-parallel kernels,
- backend-oriented lowerings that preserve denotation.

## Assumptions and Commitments

The project standardizes the distinction between assumptions, canonical commitments, and backend-specific semantics to avoid category mistakes.

### Mathematical Assumptions

Examples:

- `epsilon_r > 0`,
- alpha is in `[0, 1]`,
- weight nonnegativity,
- binary alpha,
- channel independence.

These affect truth of mathematical statements.

### Canonical Commitments

Examples:

- four-connected neighborhood,
- nearest-neighbor resize,
- clamp inside the iteration,
- the published level schedule,
- the canonical fixed-level semantics used on the main theory path.

These are not free knobs on the main line of development. They are fixed because the authored artifacts effectively choose them.

### Variant Assumptions

Examples:

- asynchronous in-place CPU iteration,
- alternate initialization policies,
- projection placement variants,
- alternate neighborhood structures explored as research variants rather than as canonical Germer semantics.

These are intentionally varied semantics and belong in relational or robustness theorems.

### Configuration Parameters

Examples:

- `epsilon_r`,
- `omega`,
- iteration counts,
- small-size threshold.

These are runtime or experimental parameters, not theorem-level commitments by themselves.

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

Three semantics are defined and kept distinct.

### Core Denotational Semantics

This semantics assigns mathematical meaning to:

- local equations,
- local solutions,
- abstract fixed-level liftings built from the local solver,
- later multilevel compositions built in the theory layer.

This semantics is the reference notion of mathematical correctness.

### Canonical Germer/PyMatting Semantics

This semantics instantiates the theory with the authored commitments fixed by the shared structure of the paper and the published CPU and GPU implementations.

It assigns meaning to:

- the canonical fixed-level update operator,
- the canonical resize and projection placement choices,
- the canonical multilevel schedule used on the main authored path.

This semantics is the reference target for backend-comparison and robustness theorems.

### Refinement Semantics

This semantics connects deep IR objects to theory-level denotations.

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
- explicit theorem dependencies on assumption bundles,
- proof that canonical commitments are separated from mathematical assumptions rather than conflated with them.

### Relational Verification

- proof that the canonical fixed-level operator is correctly lifted from the local solver,
- proof obligations for backend-specific or variant semantics relative to the canonical layer,
- explicit hypothesis tracking for initialization sensitivity, schedule sensitivity, and projection placement changes.

### Refinement Verification

- proof that each rewrite preserves denotation,
- proof that each lowered fixed-level operator matches its core or canonical shallow specification.

### Backend Validation

Executable backends, if retained, are validated against derived theory artifacts after the theory is established. Backend agreement tests are not substitutes for core theory proofs, and any backend that intentionally diverges from the canonical layer requires additional relational validation rather than simple parity checks.

## Testing Strategy

The rebuilt project will distinguish proof artifacts from validation artifacts.

Proof artifacts:

- theorem files in `Theory` and `Refinement`.

Validation artifacts:

- optional numerical comparison suites against canonical Germer/PyMatting semantics and retained backend variants,
- optional performance experiments under instantiated hardware bundles,
- backend conformance tests and discrepancy studies after relational and refinement theorems exist.

The project will not present backend smoke tests as evidence of mathematical correctness.

## Non-Goals

The initial rebuild does not attempt to:

- prove the full multilevel algorithm before the local theory is stable,
- preserve the current CLI and C++ architecture,
- force immediate backend-complete parity with every PyMatting implementation detail,
- encode all hardware models from the start,
- solve code generation before rewrite soundness is in place.

## Success Criteria

The refoundation is successful when all of the following hold:

1. The single-pixel local equation has a standalone core denotational formalization.
2. Assumptions and canonical commitments are explicit rather than hidden conventions.
3. Invertibility and closed-form theorems are reusable over the assumption lattice.
4. A canonical authored fixed-level operator is defined separately from backend-specific semantics and is lifted from the local solver.
5. A relational theorem layer exists for backend schedule, initialization, and projection variants.
6. A deep refinement IR exists with denotation and sound rewrite theorems.
7. Runtime or backend code is clearly downstream of theory rather than upstream of it.

## Recommended Next Planning Unit

The first implementation plan should cover only the initial theory kernel:

- create the new theory-oriented module tree,
- formalize the single-pixel local equation,
- define the canonical Germer/PyMatting commitments shared across the paper and the authored CPU and GPU implementations,
- define the initial assumption bundles,
- prove the first invertibility and closed-form theorem family,
- remove or isolate legacy runtime-centric modules so they do not shape the new architecture.

This scope is intentionally narrower than full multilevel formalization. It is the minimal unit that establishes the new architectural center of gravity.
