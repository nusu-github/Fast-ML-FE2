# Grid Assumptions Bridge Design

## Goal

Add a bridge from faithful two-dimensional authored grid data to the existing local theorem
kernel by supplying `CoreMathAssumptions` for canonical grid builders on a per-pixel basis.

The immediate objective is not to prove new algebraic facts. It is to make the already-proved
local theorems reusable on top of `GridPixelData` without weakening the geometry layer or
pretending that every pixel always has neighbors.

## Why This Layer Comes Next

The repository now has:

- a local theorem kernel over `LocalContext`
- a dependent-neighbor Jacobi layer
- a faithful `Pixel h w` / `ValidDir p` geometry layer
- a canonical builder that turns authored data into local contexts

What is still missing is the bridge from authored grid-side assumptions to the theorem-side
typeclass:

\[
\texttt{CoreMathAssumptions} ((data.toCanonicalPixelData).canonicalBuilder.build p state)
\]

Without that bridge, the following cannot yet be reused directly on grid-authored data:

- `Invertibility`
- `ClosedForm`
- `Conditioning`
- pointwise `Jacobi` theorems

## Design Boundary

This layer should be split into one assumption module and one theorem module.

### Assumption module

Add:

- `FastMLFE2/Theory/Assumptions/Grid.lean`

This module should define a new authored-data assumption bundle:

```lean
class GridMathAssumptions (data : GridPixelData h w) : Prop where
  epsilonPos : 0 < data.epsilonR
  omegaNonneg : 0 ≤ data.omega
  alphaBounded : ∀ p, 0 ≤ data.alpha p ∧ data.alpha p ≤ 1
```

This bundle should stay deliberately small. It should only contain what the existing
`CoreMathAssumptions`-based theorems actually need from grid-authored data.

Do **not** add `neighborNonempty` here. That condition is pixel-local and depends on
`ValidDir p`, not just on `data`.

### Theorem module

Add:

- `FastMLFE2/Theory/Theorems/GridAssumptions.lean`

This module should prove that for fixed `data`, `state`, and pixel `p`, the canonical builder
context inherits the local theorem assumptions from `GridMathAssumptions` plus an explicit
nonempty-neighbor witness.

The central theorem/instance shape should be:

```lean
instance coreMathAssumptions_of_gridMathAssumptions
    [GridMathAssumptions data]
    [Fact (Nonempty (ValidDir p))] :
    CoreMathAssumptions ((data.toCanonicalPixelData).canonicalBuilder.build p state)
```

Using an instance is preferable because it lets existing local theorems apply to grid contexts
without wrapper lemmas.

## Why `neighborNonempty` Must Stay External

The geometry layer intentionally allows degenerate grids such as `1x1`, `1xn`, and `nx1`.
For some pixels in those grids, `ValidDir p` may be empty.

So the bridge must not globally pretend that every pixel has neighbors. Instead:

- `GridMathAssumptions` carries global authored-data facts
- `Fact (Nonempty (ValidDir p))` is supplied only where the target theorem genuinely needs it

This keeps the bridge semantically honest and matches the earlier decision to avoid fake
boundary neighbors.

## Proof Contents

The bridge proof should be mostly definitional.

For the builder context

\[
ctx := (data.toCanonicalPixelData).canonicalBuilder.build p state
\]

the proof should show:

- `ctx.epsilonR = data.epsilonR`
- `ctx.omega = data.omega`
- `ctx.alphaCenter = data.alpha p`
- therefore the corresponding `epsilonPos`, `omegaNonneg`, and `alphaCenterBounded` fields follow
  from `GridMathAssumptions`
- `neighborNonempty` follows from `Fact (Nonempty (ValidDir p))`

This layer should not prove any new neighborhood-cardinality theorem. It should reuse the
geometry layer's `ValidDir p` directly.

## Non-Goals

This design does **not** yet include:

- deriving `AlphaAssumptions` for neighbor alphas
- lifting Jacobi theorems specifically to `GridPixelData`
- proving nonempty-neighbor conditions from interior/edge/corner facts
- multilevel or resize interactions

Those are the next layer after this bridge.

## Success Criteria

This design is successful if the repository gains:

- a minimal `GridMathAssumptions` bundle for authored grid data
- a theorem or instance that produces `CoreMathAssumptions` for canonical grid builder contexts
- no false global claim that every grid pixel has a neighbor

so that the existing local theorem kernel can be reused faithfully on top of the 2D grid layer.
