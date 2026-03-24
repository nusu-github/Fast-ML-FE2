# Jacobi Builder Locality Design

## Goal

Add the first locality layer above the abstract fixed-level Jacobi semantics. The purpose of this
layer is to say, in a mathematically explicit way, when a Jacobi update at pixel `p` depends only
on the old state in a designated neighborhood around `p`.

This fills the current gap in the theory:

- `Level/Jacobi` already defines simultaneous pointwise updates
- but the builder is still completely unconstrained
- so we do not yet know what part of the old state each update is allowed to observe

The locality layer gives that missing dependency law.

## Placement

Introduce two new modules:

- `FastMLFE2/Theory/Level/Locality.lean`
- `FastMLFE2/Theory/Theorems/Locality.lean`

and import the theorem module from `FastMLFE2/Theory.lean`.

`Level/Locality` should contain only the abstract dependency notions.
`Theorems/Locality` should contain the consequences for `builder.build`, `jacobiUpdateAt`, and
`jacobiStep`.

## Core Abstractions

### Neighborhoods

Use finite neighborhoods from the start:

\[
\texttt{Neighborhood}\;\kappa := \kappa \to \texttt{Finset}\;\kappa.
\]

The design chooses `Finset κ` instead of `κ → Prop` because later authored neighborhoods, actual
neighbor enumeration, and implementation refinement all want explicit finite carriers.

### State agreement on a set

Define:

\[
\texttt{StateEqOn}\;S\;s_1\;s_2 := \forall q,\ q \in S \to s_1 q = s_2 q.
\]

This is the minimal relation needed to express observational locality. It should stay completely
extensional and should not assume anything about geometry or image structure.

### Builder locality

The locality law itself should remain a theorem hypothesis, not a class:

\[
\texttt{BuilderLocal}\;builder\;N :=
\forall p\, s_1\, s_2,\ 
\texttt{StateEqOn}\;(N\,p)\;s_1\;s_2 \to
builder.build\;p\;s_1 = builder.build\;p\;s_2.
\]

This says only that `builder.build p` is insensitive to state changes outside `N p`.

At this stage, locality is intentionally expressed in terms of observable equality of the built
`LocalContext`, not in terms of fieldwise implementation structure such as “only
`fgNeighbor`/`bgNeighbor` depend on state”.

## Why Extensional Locality First

There are two possible locality layers:

1. extensional locality:
   `state₁` and `state₂` agree on `N p` implies `builder.build p state₁ = builder.build p state₂`
2. fieldwise/authored locality:
   some fields are fixed data, other fields depend on state only through neighborhood lookups

This design chooses the first one now.

The reason is that the current level semantics is still abstract. We want to prove that Jacobi
updates are neighborhood-local before committing to the more authored Germer/PyMatting structure
of the builder. Fieldwise locality is still valuable, but it belongs to a later canonical-builder
layer.

## Theorem Layer

The first theorem batch should stay small and direct.

### Builder locality theorem

From `BuilderLocal builder N`, we can restate directly that:

\[
\texttt{StateEqOn}\;(N\,p)\;s_1\;s_2 \to
builder.build\;p\;s_1 = builder.build\;p\;s_2.
\]

This sounds trivial, but it is useful as the named handoff theorem for later modules.

### Jacobi update locality

Since `jacobiUpdateAt builder state p` is defined by applying `closedFormSolution` to
`builder.build p state`, locality of the builder should immediately imply:

\[
\texttt{StateEqOn}\;(N\,p)\;s_1\;s_2 \to
builder.jacobiUpdateAt\;s_1\;p = builder.jacobiUpdateAt\;s_2\;p.
\]

### Jacobi step pointwise locality

Likewise:

\[
\texttt{StateEqOn}\;(N\,p)\;s_1\;s_2 \to
builder.jacobiStep\;s_1\;p = builder.jacobiStep\;s_2\;p.
\]

This is the first mathematically explicit statement that the simultaneous update at pixel `p`
depends only on a designated neighborhood of the old state.

## What This Unlocks

This layer is the right successor to the current abstract Jacobi semantics.

- It explains what “pointwise simultaneous update” is allowed to observe.
- It gives the first clean route toward a formal parallel-independence story.
- It provides the bridge needed before adding authored builders, 2D neighborhoods, and schedule
  comparisons.

Without this layer, the Jacobi semantics is correct but still too unconstrained to support serious
reasoning about locality, parallelism, or backend schedule differences.

## Non-Goals

This design does **not** yet include:

- 2D coordinates
- specific 4-neighbor or 8-neighbor laws
- neighborhood symmetry
- self-membership laws
- authored fixed-data versus state-dependent field splits
- convergence or iteration-count theorems
- Gauss-Seidel or async comparisons

Those belong to later layers.

## Success Criteria

This design is successful if the repository gains:

- a reusable `Neighborhood` abstraction
- a reusable `StateEqOn` relation
- a reusable `BuilderLocal` predicate
- pointwise locality theorems for `builder.build`, `jacobiUpdateAt`, and `jacobiStep`

without prematurely baking in geometric image structure or authored builder internals.
