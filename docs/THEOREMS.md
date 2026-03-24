# Theorem Inventory

This document summarizes the machine-checked results that are currently available in the
theory layer, together with the conditions under which they hold. It is intended as a
user-facing inventory of what is already proved, not as a replacement for the source files.

Unless stated otherwise, theorem module paths are relative to the repository root.

## Assumption Bundles Used Throughout

### `CoreMathAssumptions`

Defined in `FastMLFE2/Theory/Assumptions/Bundles.lean`.

Most local closed-form / conditioning / Jacobi theorems assume:

- `0 < ctx.epsilonR`
- `0 ≤ ctx.omega`
- `0 ≤ ctx.alphaCenter ≤ 1`
- `Nonempty ι`

This is the default local well-posedness bundle for the single-pixel theory.

### `GridMathAssumptions`

Defined in `FastMLFE2/Theory/Assumptions/Grid.lean`.

Used by grid-specialized results. These assumptions are then bridged to pointwise
`CoreMathAssumptions` by `FastMLFE2/Theory/Theorems/GridAssumptions.lean`.

### `BuilderLocal`

Defined in `FastMLFE2/Theory/Level/Locality.lean`.

Used by locality / propagation theorems. It expresses that a builder depends only on the
designated neighborhood of a pixel.

## Stage-Oriented Summary

### Stage 1 — Formal Specification

- Local 2×2 normal equation and local cost semantics:
  `FastMLFE2/Theory/Core/LocalEquation.lean`,
  `FastMLFE2/Theory/Core/LocalSemantics.lean`
- Canonical commitments (4-neighborhood, authored builder conventions, resize schedule):
  `FastMLFE2/Theory/Canonical/*`
- Idealized Blur-Fusion approximation semantics:
  `FastMLFE2/Theory/Approximation/BlurFusion.lean`

These files are mostly definitional. The theorem inventory below focuses on the imported
`FastMLFE2/Theory/Theorems/*.lean` modules that state proved results over this foundation.

### Stage 2 — Design-Space Exploration

This stage includes theorems that characterize when the local system is invertible, when it
degenerates in special cases, which quantities can be reused across channels, how clamping
behaves, and which simplifications fail by explicit counterexample.

### Stage 3 — Deductive Synthesis / Refinement

This stage includes the closed-form solver proof, the cost-to-normal-equation bridge, Jacobi
fixed-point / contraction theorems, locality propagation bounds, and canonical/grid lifting
results that expose optimized forms under proved equalities.

## Exhaustive Theorem Module Inventory

### 1. `FastMLFE2/Theory/Theorems/Invertibility.lean`

**Main content**

- Neighbor weights are nonnegative / positive.
- `totalWeight > 0`.
- The normal-matrix determinant has the expected closed form.
- The determinant is positive, nonzero, and a unit.

**Conditions**

- `CoreMathAssumptions ctx`

**Interpretation**

- The local 2×2 normal equation is well-posed under the standard positivity and bounded-alpha
  assumptions.

### 2. `FastMLFE2/Theory/Theorems/ClosedForm.lean`

**Main content**

- Defines `closedFormDenom`, `closedFormForegroundNumerator`,
  `closedFormBackgroundNumerator`, and `closedFormSolution`.
- Proves that the explicit 2×2 closed form solves the normal equation.
- Proves equality with the matrix-inverse solution.
- Proves cost stationarity of the closed-form solution.

**Conditions**

- `CoreMathAssumptions ctx`

**Interpretation**

- The authored closed form is mathematically correct and unique whenever the local system is
  invertible.

### 3. `FastMLFE2/Theory/Theorems/ClosedFormBox.lean`

**Main content**

- If the foreground/background numerators lie between `0` and `closedFormDenom`, then the
  corresponding closed-form components lie in `[0, 1]`.
- Under those bounds, `clamp01 (closedFormSolution ctx) = closedFormSolution ctx`.
- If there exists any boxed solution of the normal equation, then the closed-form solution is
  already boxed.

**Conditions**

- `CoreMathAssumptions ctx`
- Additional theorem-specific hypotheses bounding the closed-form numerators, or the existence
  of a boxed normal-equation solution.

**Interpretation**

- Box preservation is proved from precise numerator bounds, not from naive input boundedness.

### 4. `FastMLFE2/Theory/Theorems/ClosedFormBoxInput.lean`

**Main content**

- Explicit counterexample showing that boxed inputs alone do **not** imply a boxed
  closed-form solution.
- Weighted-mean decomposition of the closed-form denominator and numerators.
- Foreground/background solutions rewritten as weighted-mean affine forms.
- Exact iff criteria for solution components to lie in `[0, 1]`.
- Exact iff / sufficient criteria for `clamp01` to be the identity.

**Conditions**

- Counterexample theorems: specialized explicit context, no global hypothesis beyond the
  constructed data.
- Structural weighted-mean theorems: mostly `CoreMathAssumptions ctx`.
- Box-membership theorems: additional component-wise weighted-mean bounds.

**Interpretation**

- This module both disproves the naive boxed-input claim and replaces it with the correct
  weighted-mean criteria.

### 5. `FastMLFE2/Theory/Theorems/CostToNormalEquation.lean`

**Main content**

- Expands foreground / background one-dimensional line costs exactly as quadratics in the
  perturbation parameter.
- Proves genuine `HasDerivAt` derivatives for those line costs.
- Proves `ctx.IsCostStationary g ↔ ctx.SolvesNormalEquation g`.

**Conditions**

- No extra global hypothesis is required for the equivalence theorem itself; it is an exact
  symbolic result over the local definitions.

**Interpretation**

- The local normal equation is exactly the first-order stationarity condition of the cost.

### 6. `FastMLFE2/Theory/Theorems/Conditioning.lean`

**Main content**

- Rank-1 decomposition of the normal matrix.
- Exact eigenvalue formulas.
- Exact condition-number formula `κ = 1 + q(α) / totalWeight`.
- Bounds on `q(α)` and therefore on `κ`.
- Special values at `α = 0`, `α = 1`, and `α = 1/2`.

**Conditions**

- `CoreMathAssumptions ctx`
- Special-case theorems additionally assume `ctx.alphaCenter = 0`, `1`, or `1/2`.

**Interpretation**

- The conditioning of the local system is fully characterized under the core assumptions.

### 7. `FastMLFE2/Theory/Theorems/BinaryAlpha.lean`

**Main content**

- If `ctx.alphaCenter = 0` or `ctx.alphaCenter = 1`, the normal matrix simplifies to a
  diagonal form.
- The RHS and denominator simplify accordingly.
- The closed-form solution becomes componentwise separable.

**Conditions**

- The local context must satisfy the binary-alpha hypothesis
  `ctx.alphaCenter = 0` or `ctx.alphaCenter = 1`.

**Interpretation**

- Binary alpha collapses the coupled 2×2 system into independent scalar subproblems.

### 8. `FastMLFE2/Theory/Theorems/BinaryAlphaCost.lean`

**Main content**

- The local cost simplifies in the binary-alpha cases.
- Cost stationarity becomes an iff condition on decoupled scalar equations.

**Conditions**

- Binary-alpha hypothesis (`ctx.alphaCenter = 0` or `1`).

**Interpretation**

- This is the cost-side companion to the matrix simplifications in `BinaryAlpha.lean`.

### 9. `FastMLFE2/Theory/Theorems/ChannelReuse.lean`

**Main content**

- Defines `SameWeightData`: exactly the data needed to reuse neighbor weights and the normal
  matrix across channels.
- Defines `SameRhsData`: exactly the stronger data needed to reuse the RHS as well.
- Proves equality of neighbor weights, `totalWeight`, the normal matrix, and the closed-form
  denominator under `SameWeightData`.
- Proves equality of foreground/background sums and of the RHS under `SameRhsData`.
- Gives an explicit counterexample showing that shared weight data alone does **not** imply
  shared RHS.

**Conditions**

- Equality assumptions encoded by `SameWeightData` / `SameRhsData`.

**Interpretation**

- Matrix reuse across RGB is justified, but RHS reuse requires stronger signal-side equality.

### 10. `FastMLFE2/Theory/Theorems/ClampLocal.lean`

**Main content**

- Characterizes exactly when `clamp01` is the identity.
- Gives sufficient component-wise bounds implying that `clamp01` does nothing to the
  closed-form solution.

**Conditions**

- Pure algebraic theorems; no special global assumption bundle.

**Interpretation**

- This module isolates the local mathematics of clamping itself.

### 11. `FastMLFE2/Theory/Theorems/CompositingError.lean`

**Main content**

- General triangle-inequality bound for one-channel compositing error.
- Authored tighter form when `0 ≤ α ≤ 1`.

**Conditions**

- General bound: no extra condition.
- Authored bound: `0 ≤ α ∧ α ≤ 1`.

**Interpretation**

- Foreground/background approximation error propagates linearly through compositing.

### 12. `FastMLFE2/Theory/Theorems/JacobiContraction.lean`

**Main content**

- Exact algebra for one-step / two-step Jacobi differences.
- Positivity of Jacobi diagonal terms and nonnegativity of the cross term.
- Closed form for the local Jacobi spectral radius.
- Proof that the spectral radius is `< 1` under the core assumptions.
- Immediate-convergence special cases when `α = 0` or `α = 1`.
- Infinity-norm contraction bounds for two-step and multi-step iterates.
- Closed form is a Jacobi fixed point.
- Error bounds for iterative convergence to the closed form.

**Conditions**

- `CoreMathAssumptions ctx` for positivity, spectral-radius, and contraction theorems.
- Binary-alpha subresults additionally assume `ctx.alphaCenter = 0` or `1`.

**Interpretation**

- Jacobi iteration is formally controlled and convergent in the local theory kernel.

### 13. `FastMLFE2/Theory/Theorems/BlurFusionGap.lean`

**Main content**

- Exact joint stage-two Blur-Fusion solution in a synthetic one-neighbor model.
- Exact sequential-vs-joint gap formula.
- Absolute upper bounds on that gap under boxed inputs.

**Conditions**

- Typically `0 ≤ α ≤ 1` plus boxed signal/neighbor inputs for the absolute bound theorems.

**Interpretation**

- The approximation gap of sequential Blur-Fusion is quantified exactly in a canonical
  reduced setting.

### 14. `FastMLFE2/Theory/Theorems/BlurFusionFixedPoint.lean`

**Main content**

- Explicit counterexample builder showing that the first Blur-Fusion update need not equal the
  Jacobi update.
- Explicit counterexample showing that the first Blur-Fusion stage is not a fixed point of the
  Blur-Fusion dynamics.
- Exact iff characterization of a special fixed-point condition in the constructed example.

**Conditions**

- Specialized explicit counterexample context / builder.

**Interpretation**

- This module records a genuine limitation of Blur-Fusion style updates.

### 15. `FastMLFE2/Theory/Theorems/PropagationRadius.lean`

**Main content**

- Defines the recursively expanded `k`-step propagation neighborhood.
- Recursive membership characterization for the propagation neighborhood.
- Proves that repeated Jacobi and Blur-Fusion iterates depend only on the corresponding
  propagation neighborhood.
- In particular, proves 1-step and 2-step locality for the named Blur-Fusion intermediate
  updates.

**Conditions**

- `BuilderLocal build`
- Equality of input states on the relevant neighborhood (`StateEqOn` hypotheses).

**Interpretation**

- Fixed-level propagation has formally bounded spatial support.

### 16. `FastMLFE2/Theory/Theorems/NearBinary.lean`

**Main content**

- Quantifies deviation from the binary-alpha system when alpha is near binary.
- Shows that boxed neighbors imply boxed weighted sums / means.
- Gives exact formulas and upper bounds for the distance between the closed-form foreground
  solution and the foreground mean.
- Provides an explicit near-binary counterexample where the clamped unconstrained solution is
  more expensive than the binary-alpha solution.

**Conditions**

- Structural deviation / box-propagation theorems use local hypotheses on alpha and boxed
  neighbor values.
- The negative-result theorems are specialized to an explicit constructed context.

**Interpretation**

- Near-binary alpha is not the same as binary alpha, and naive clamp-after-solve behavior can
  be suboptimal.

### 17. `FastMLFE2/Theory/Theorems/NearBinaryCounterexample.lean`

**Main content**

- Dedicated counterexample data supporting the near-binary negative results.

**Conditions**

- Specialized explicit context.

**Interpretation**

- This file packages the explicit witness showing the limits of near-binary simplifications.

### 18. `FastMLFE2/Theory/Theorems/ClampPlacement.lean`

**Main content**

- Exact formula for the raw unconstrained one-step gain.
- Proof that the raw step can be non-contractive.
- Proof that scalar clamp, vector clamp, and statewise clamp are nonexpansive.

**Conditions**

- Gain theorems use `CoreMathAssumptions ctx`.
- Clamp nonexpansiveness theorems are purely algebraic.

**Interpretation**

- Clamping is formally safe in the Lipschitz sense, but the unclamped raw step may expand.

### 19. `FastMLFE2/Theory/Theorems/ClampPlacementCounterexample.lean`

**Main content**

- Explicit counterexample data with exact iterate values.
- Exact raw gain value greater than `1`.
- Proof that clamping inside the iteration and clamping at the end can produce different
  outputs.

**Conditions**

- Specialized explicit counterexample configuration.

**Interpretation**

- Clamp placement is not an innocuous implementation detail; the theorem layer records the
  divergence explicitly.

### 20. `FastMLFE2/Theory/Theorems/BleedThrough.lean`

**Main content**

- Bounds local foreground/background error by Jacobi iterate error.
- Bounds compositing error after Jacobi iteration.
- Gives tighter boxed-solution bounds.
- Gives a logarithmic threshold theorem connecting target error to a sufficient iteration
  count.

**Conditions**

- `CoreMathAssumptions ctx` for the iterative error theorems.
- Additional boxedness hypotheses for the tighter boxed variants.
- Additional threshold hypotheses for the iteration-count result.

**Interpretation**

- This module quantifies how iterative local error leaks into compositing error.

### 21. `FastMLFE2/Theory/Theorems/Jacobi.lean`

**Main content**

- `jacobiUpdateAt` coincides with the local closed form.
- Therefore each Jacobi-updated pixel solves the local normal equation.
- Therefore each Jacobi-updated pixel is cost-stationary.

**Conditions**

- Pointwise `CoreMathAssumptions` for the built local context.

**Interpretation**

- The simultaneous Jacobi update is not merely heuristic: each updated pixel is the proved
  local solution.

### 22. `FastMLFE2/Theory/Theorems/Locality.lean`

**Main content**

- If two states agree on the relevant neighborhood, the builder outputs agree.
- Under the same locality hypothesis, `jacobiUpdateAt` agrees.
- Consequently the whole `jacobiStep` agrees on that pixel.

**Conditions**

- `BuilderLocal build`
- `StateEqOn` agreement on the designated neighborhood.

**Interpretation**

- Builder locality lifts directly to Jacobi locality.

### 23. `FastMLFE2/Theory/Theorems/Grid.lean`

**Main content**

- The canonical grid neighborhood equals the 4-neighbor neighborhood.
- Exact cardinality theorems for valid directions:
  - interior: `4`
  - non-corner edges: `3`
  - corners: `2`

**Conditions**

- Geometry predicates such as `IsInterior`, `IsTopEdgeNoncorner`, `IsTopLeftCorner`, etc.

**Interpretation**

- The authored grid geometry is formalized exactly and combinatorially.

### 24. `FastMLFE2/Theory/Theorems/GridNonempty.lean`

**Main content**

- Constructive `Nonempty (ValidDir p)` witnesses for interior, edge, and corner cases.

**Conditions**

- The corresponding geometric hypotheses (`IsInterior`, edge/corner predicates).

**Interpretation**

- These witness the nonemptiness assumptions needed to instantiate the local theory on grid
  pixels.

### 25. `FastMLFE2/Theory/Theorems/GridAssumptions.lean`

**Main content**

- Bridges grid-level assumptions to pointwise `CoreMathAssumptions` on the local context
  extracted from grid pixel data.

**Conditions**

- `GridMathAssumptions` plus local neighbor nonemptiness supplied by the geometric side.

**Interpretation**

- This is the main assumption-lifting bridge from global grid data to local algebra.

### 26. `FastMLFE2/Theory/Theorems/InteriorKernel.lean`

**Main content**

- Interior-pixel valid directions are canonically equivalent to the four cardinal directions.
- Interior grid total weight, sums, RHS, normal matrix, denominator, numerators, and closed
  form all agree with the specialized interior-kernel formulas.

**Conditions**

- `IsInterior p`

**Interpretation**

- The optimized interior 4-neighbor kernel is proved equivalent to the general grid-local
  semantics at interior pixels.

### 27. `FastMLFE2/Theory/Theorems/GridLocal.lean`

**Main content**

- Re-exposes local closed-form theorems for `GridPixelData.localCtx`.
- In particular, proves that the grid-local closed form solves the normal equation and is
  cost-stationary.

**Conditions**

- Grid-local assumptions sufficient to instantiate `CoreMathAssumptions`, typically
  `GridMathAssumptions` together with `Nonempty (ValidDir p)`.

**Interpretation**

- This is a thin wrapper layer specializing the generic local theorems to grid data.

### 28. `FastMLFE2/Theory/Theorems/CanonicalBuilder.lean`

**Main content**

- Simplification theorems exposing the fields of the authored canonical builder.
- Proof that the canonical builder satisfies `BuilderLocal`.

**Conditions**

- No extra mathematical assumption bundle; these are definitional / structural theorems.

**Interpretation**

- The authored builder is certified as a valid instance of the abstract locality interface.

## Counterexample / Negative-Result Modules at a Glance

The repository does not only prove positive properties. It also contains dedicated negative
results:

- `ClosedFormBoxInput.lean`:
  boxed inputs do **not** imply boxed closed-form outputs.
- `BlurFusionFixedPoint.lean`:
  the first Blur-Fusion update need not equal the Jacobi update and need not be a fixed point.
- `NearBinary.lean` and `NearBinaryCounterexample.lean`:
  near-binary unconstrained-then-clamp can be worse than the binary-alpha solution.
- `ClampPlacementCounterexample.lean`:
  clamping inside the iteration and clamping at the end can diverge.
- `ChannelReuse.lean`:
  shared weight data alone do **not** force shared RHS data.

## Suggested Reading Order

If you want to reconstruct the current proof landscape quickly, a practical order is:

1. `Invertibility.lean`
2. `CostToNormalEquation.lean`
3. `ClosedForm.lean`
4. `Conditioning.lean`
5. `BinaryAlpha.lean` and `BinaryAlphaCost.lean`
6. `ClosedFormBox.lean` and `ClosedFormBoxInput.lean`
7. `JacobiContraction.lean`
8. `Jacobi.lean`, `Locality.lean`, `PropagationRadius.lean`
9. `CanonicalBuilder.lean`, `Grid*.lean`, `InteriorKernel.lean`
10. Counterexample modules for limits and backend divergences
