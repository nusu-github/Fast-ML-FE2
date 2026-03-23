# Canonical Builder Design

## Goal

Add the first authored builder layer above the abstract Jacobi and locality semantics. This layer
should model the Germer/PyMatting-style situation where:

- alpha data is fixed image data
- image values are fixed image data
- the neighbor relation is fixed by a neighborhood lookup
- only foreground/background neighbor values are read from the current Jacobi state

The immediate goal is to construct a canonical `LocalContextBuilder` from this authored data and
prove that it satisfies the previously introduced abstract locality law.

## Placement

Introduce two new modules:

- `FastMLFE2/Theory/Canonical/Builder.lean`
- `FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`

and import the theorem module from `FastMLFE2/Theory.lean`.

`Canonical/Builder` should contain the authored data bundle and the construction of the builder
and induced neighborhood. `Theorems/CanonicalBuilder` should prove that the builder fields match
the intended authored semantics and that the resulting builder is local.

## Canonical Pixel Data

Define a data bundle:

```lean
structure CanonicalPixelData (κ ι : Type*) where
  alpha : κ → ℝ
  image : κ → ℝ
  neighborPixel : κ → ι → κ
  epsilonR : ℝ
  omega : ℝ
```

At this stage, `epsilonR` and `omega` should remain global scalars, not pixel-dependent fields.
That matches the present theory and avoids an unnecessary generalization.

Likewise, `alphaNeighbor` should not be stored separately. It should be derived by following the
neighbor lookup through `alpha`.

## Canonical Builder Construction

Given `data : CanonicalPixelData κ ι` and `state : PixelState κ`, define the local context at
pixel `p` by:

- `alphaCenter := data.alpha p`
- `imageValue := data.image p`
- `alphaNeighbor j := data.alpha (data.neighborPixel p j)`
- `fgNeighbor j := foreground (state (data.neighborPixel p j))`
- `bgNeighbor j := background (state (data.neighborPixel p j))`
- `epsilonR := data.epsilonR`
- `omega := data.omega`

This produces:

\[
\texttt{toLocalContext}\;data\;p\;state : LocalContext ι
\]

and then:

\[
\texttt{canonicalBuilder}\;data : LocalContextBuilder κ ι.
\]

## Induced Neighborhood

The locality proof should not require a separately stored neighborhood.
Instead, define the neighborhood induced by the authored neighbor lookup:

\[
\texttt{canonicalNeighborhood}\;data\;p :=
(\texttt{Finset.univ}).\texttt{image} (data.neighborPixel\;p).
\]

This is the correct extensional neighborhood for the builder because these are exactly the pixel
indices whose state values are read in the foreground/background neighbor fields.

## Theorem Layer

The theorem batch should focus on two things.

### Field correctness

Add direct theorems stating that the canonical builder computes the intended fields:

- `alphaCenter`
- `imageValue`
- `alphaNeighbor`
- `fgNeighbor`
- `bgNeighbor`
- `epsilonR`
- `omega`

These should be simple `rfl`/`simp`-style theorems. Their purpose is to prevent the authored
builder from becoming opaque later.

### Locality theorem

Prove:

\[
\texttt{BuilderLocal}\;(\texttt{canonicalBuilder}\;data)\;(\texttt{canonicalNeighborhood}\;data).
\]

The proof should work by:

1. assuming two states agree on `canonicalNeighborhood data p`
2. showing the `foreground` and `background` values read through every `neighborPixel p j`
   are equal in both states
3. extensionality on the resulting `LocalContext`

Because all non-state fields are fixed data and all state-dependent fields are read only through
`neighborPixel`, the proof should be direct and definition-driven.

## Why This Next

This layer is the correct successor to the abstract locality layer.

- `Level/Jacobi` defines simultaneous updates
- `Level/Locality` defines what it means for a builder to be local
- this canonical builder layer shows that the Germer/PyMatting-style authored builder actually
  satisfies that abstract law

Without this layer, locality remains a useful abstraction but not yet connected to the intended
foreground-estimation semantics.

## Non-Goals

This design does **not** yet include:

- 2D image coordinates
- 4-neighbor or 8-neighbor geometry facts
- boundary handling
- proofs of `CoreMathAssumptions`
- iteration or convergence results
- multilevel lifting

Those are later layers.

## Success Criteria

This design is successful if the repository gains:

- a reusable `CanonicalPixelData` bundle
- a concrete `canonicalBuilder`
- an induced `canonicalNeighborhood`
- field-level theorems exposing the authored construction
- a proof that the canonical builder satisfies the abstract `BuilderLocal` law

so that the abstract Jacobi/locality semantics is concretely connected to the intended authored
foreground-estimation data flow.
