# Grid Nonempty Design

## Summary

Add a small theorem layer that supplies concrete witnesses for
`Nonempty (ValidDir p)` on faithful 2D four-neighbor grids. This is the next
bridge between the boundary-aware geometry layer and the existing local solver
kernel, which currently requires `Fact (Nonempty (ValidDir p))` to instantiate
`CoreMathAssumptions` on a grid pixel.

This layer is intentionally theorem-only. It does not add typeclass automation,
does not change the geometry core, and does not yet try to classify all
degenerate `1 × n` or `n × 1` grids.

## Goal

Make it explicit, in Lean, which authored geometric cases support local solver
theorems:

- interior pixels,
- noncorner boundary pixels,
- corners on genuinely two-dimensional grids.

The result should be a set of small witness theorems that later grid-Jacobi
wrappers can turn into local `Fact (Nonempty (ValidDir p))` instances.

## Chosen Approach

### Theorem-Only Layer

Create a new module:

- `FastMLFE2/Theory/Theorems/GridNonempty.lean`

This module will export theorems of the form:

- `nonempty_validDir_of_isInterior`
- `nonempty_validDir_of_isTopEdgeNoncorner`
- `nonempty_validDir_of_isBottomEdgeNoncorner`
- `nonempty_validDir_of_isLeftEdgeNoncorner`
- `nonempty_validDir_of_isRightEdgeNoncorner`
- `nonempty_validDir_of_isTopLeftCorner`
- `nonempty_validDir_of_isTopRightCorner`
- `nonempty_validDir_of_isBottomLeftCorner`
- `nonempty_validDir_of_isBottomRightCorner`

Theorems will return `Nonempty (ValidDir p)` directly, not `Fact (...)`
instances. That keeps the geometry layer explicit and avoids hiding case
analysis inside instance search.

### Witness-First Proof Style

Proofs will be constructive and direct:

- interior: use `up` as the witness;
- top edge noncorner: use `down`;
- bottom edge noncorner: use `up`;
- left edge noncorner: use `right`;
- right edge noncorner: use `left`;
- corners: pick one in-bounds direction, under the same dimensional hypotheses
  already used by the corner cardinality theorems.

This avoids a detour through cardinality lemmas. The purpose of this layer is
to prove applicability, not to recompute neighbor counts.

## Scope Boundaries

### Included

- constructive `Nonempty (ValidDir p)` theorems for the authored interior,
  edge-noncorner, and corner cases;
- import into `FastMLFE2/Theory.lean`.

### Explicitly Deferred

- automatic `Fact (Nonempty (ValidDir p))` instances;
- exhaustive handling of degenerate `1 × n` and `n × 1` grids;
- grid-specific Jacobi wrappers;
- any change to `Canonical.Grid` or the local algebra core.

## Rationale

This cut keeps the current question small: "when does a grid pixel have at
least one faithful neighbor?" It isolates geometry from later theorem lifting.
If there is a problem, it will be in the witness geometry, not in typeclass
automation or Jacobi wrappers.

That matches the current architecture:

1. faithful geometry,
2. local assumption bridge,
3. nonempty witness theorems,
4. grid-level theorem lifting.

