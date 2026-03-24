# H11a Compositing Error Design

## Goal

Add a new `Theory/Compositing` layer that formalizes one-channel alpha compositing and proves
the first practical quality theorem for foreground estimation:

\[
|\alpha F + (1-\alpha) B - (\alpha F^* + (1-\alpha) B^*)|
\le |\alpha|\,|F-F^*| + |1-\alpha|\,|B-B^*|.
\]

This is the `H11a` bridge from local estimation error to recomposited image error. It is kept
separate from the local solver kernel so that solver correctness and compositing-quality results
do not get mixed into the same core module.

## Placement

Introduce a new layer:

- `FastMLFE2/Theory/Compositing/OneChannel.lean`
- `FastMLFE2/Theory/Theorems/CompositingError.lean`

and import the theorem module from `FastMLFE2/Theory.lean`.

The compositing semantics lives outside `Theory/Core` because it is not part of the local
foreground-estimation equation itself. It is a downstream quality semantics for how estimated
`F` and `B` affect a recomposited pixel.

## Semantics

The base definition is one-channel compositing over `ℝ`:

\[
\operatorname{compose}(\alpha, F, B) := \alpha F + (1-\alpha) B.
\]

The first theorem layer should remain scalar and channel-agnostic. RGB lifting can happen later
through channel-wise application.

## Theorem Structure

The theorem stack should be split into two tiers.

### Tier 1: Unconditional algebraic error bound

Prove directly from ring algebra and the triangle inequality:

\[
|\operatorname{compose}(\alpha, F, B) - \operatorname{compose}(\alpha, F^*, B^*)|
\le |\alpha|\,|F-F^*| + |1-\alpha|\,|B-B^*|.
\]

This theorem should not assume `0 ≤ α ≤ 1`. It is a pure algebraic identity plus `abs_add` and
`abs_mul`.

### Tier 2: Authored alpha-matting corollary

Under `0 ≤ α ≤ 1`, simplify the weights to:

\[
|\operatorname{compose}(\alpha, F, B) - \operatorname{compose}(\alpha, F^*, B^*)|
\le \alpha\,|F-F^*| + (1-\alpha)\,|B-B^*|.
\]

This is the form that should be cited in later quality discussions, because it matches the
semantics of alpha compositing and makes the asymmetry between foreground and background errors
explicit.

## Why This Next

This is the right successor to `H12`.

- `H12` tells us where the local solve is numerically sensitive.
- `H11a` tells us how foreground/background estimation error actually enters the final
  recomposited pixel.

Together they separate:

- numerical sensitivity of the estimator
- visual impact of the resulting error under compositing

That separation is important because `α ≈ 0` can be numerically ill-conditioned while still
having small direct compositing weight on the foreground term.

## Non-Goals

This design does **not** yet include:

- image-wide norms
- RGB/vector norms
- iterative propagation guarantees
- bleed-through guarantees
- clamp or projection effects

Those belong to later layers.

## Success Criteria

This design is successful if the repository gains:

- a standalone one-channel compositing semantics
- an unconditional absolute-value recomposition error theorem
- an authored `0 ≤ α ≤ 1` corollary
- a clean import path from the theory umbrella

without coupling compositing quality semantics to the local solver core.
