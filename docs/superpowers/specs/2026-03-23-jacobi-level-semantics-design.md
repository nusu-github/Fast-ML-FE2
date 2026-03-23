# Jacobi Level Semantics Design

## Goal

Add the first fixed-level update semantics above the local single-pixel kernel. The new layer
defines a simultaneous Jacobi-style one-step update on a finite pixel index set and proves that
each updated pixel value is the closed-form local solution of its own local context.

This is the missing bridge between:

- the already-proved local solver kernel
- future reasoning about iteration schemes, backend schedules, and multilevel lifting

## Placement

Introduce two new modules:

- `FastMLFE2/Theory/Level/Jacobi.lean`
- `FastMLFE2/Theory/Theorems/Jacobi.lean`

and import the theorem module from `FastMLFE2/Theory.lean`.

`Level/Jacobi` should contain only the new fixed-level semantics and definitional lemmas.
`Theorems/Jacobi` should contain the proofs that lift existing local theorems pointwise to the
whole-image Jacobi step.

## Core Abstractions

The first Jacobi layer should stay abstract over the image representation.

### Pixel state

For a pixel index type `κ`, define:

\[
\texttt{PixelState}\;\kappa := \kappa \to \texttt{LocalUnknown}.
\]

This means a whole image state is just a mapping from pixel index to the local pair
`(F_i^c, B_i^c)`.

### Local context builder

Define:

```lean
structure LocalContextBuilder (κ ι : Type*) [Fintype ι] where
  build : κ → PixelState κ → LocalContext ι
```

The builder is intentionally free at this layer. It is not yet constrained to authored Germer
data flow such as "only `fgNeighbor`/`bgNeighbor` depend on the current state". Those constraints
belong to later builder-assumption layers.

### Jacobi update

Define:

\[
\texttt{jacobiUpdateAt}\;builder\;state\;p := \texttt{closedFormSolution}\;(builder.build\;p\;state)
\]

and

\[
\texttt{jacobiStep}\;builder\;state := \lambda p,\ \texttt{jacobiUpdateAt}\;builder\;state\;p.
\]

This is a true simultaneous update semantics because every new pixel value is computed from the
same old `state`.

## Theorem Layer

The first theorem batch should be intentionally small and pointwise.

### Definitional theorem

Prove the expected application lemma:

\[
\texttt{jacobiStep}\;builder\;state\;p
= \texttt{closedFormSolution}\;(builder.build\;p\;state).
\]

### Pointwise normal-equation theorem

Under `CoreMathAssumptions (builder.build p state)`, prove:

\[
(\texttt{builder.build}\;p\;state).\texttt{SolvesNormalEquation}
  (\texttt{jacobiStep}\;builder\;state\;p).
\]

This should be a direct lift of `closedForm_solvesNormalEquation`.

### Pointwise stationary theorem

Under the same assumptions, prove:

\[
(\texttt{builder.build}\;p\;state).\texttt{IsCostStationary}
  (\texttt{jacobiStep}\;builder\;state\;p).
\]

This should be a direct lift of `closedForm_isCostStationary`.

## Why This Shape

This layer is deliberately thin.

- It does **not** commit yet to 2D coordinates.
- It does **not** commit yet to authored neighborhood dependence.
- It does **not** commit yet to multilevel schedules.
- It does **not** commit yet to GPU or CPU backend details.

That is intentional. The purpose of this layer is only to define what one simultaneous level
update means, independently of how local contexts are later built from authored image data.

## Non-Goals

This design does **not** yet include:

- 2D image indexing
- neighborhood locality laws
- Gauss-Seidel or async schedules
- convergence results
- multilevel lifting
- backend equivalence results

Those are downstream of this fixed-level semantics.

## Success Criteria

This design is successful if the repository gains:

- a reusable `PixelState` abstraction
- a reusable `LocalContextBuilder` abstraction
- a function-valued `jacobiStep`
- pointwise theorems showing each Jacobi-updated pixel is a local closed-form / normal-equation /
  stationary solution

without prematurely baking in authored image structure or backend-specific assumptions.
