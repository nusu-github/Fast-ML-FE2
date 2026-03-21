# Fast-ML-FE2

This repository has two intentionally separate layers:

- `spec`: Lean models and proofs for the simultaneous-update local refinement specification.
- `reference`: the executable foreground estimator, aligned with the pymatting-style multi-level solver.

The executable `reference` solver is the supported runtime path. The Lean `spec` layer is a proof target and
does not claim identical step semantics with the native iterative solver.
