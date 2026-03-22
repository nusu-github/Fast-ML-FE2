# Fast-ML-FE2

This repository has two intentionally separate layers:

- `theory`: the new Lean source of truth for the refounded Fast Multi-Level Foreground
  Estimation kernel.
- `legacy`: the older runtime, CLI, and native comparison infrastructure.

`FastMLFE2.Theory` is the primary library surface. It formalizes the raw local equation,
canonical authored commitments, explicit assumption bundles, and the first local theorem
kernel without letting native dependencies or backend scheduling choices define correctness.

The runtime, CLI, and native code remain available through `FastMLFE2.Legacy`, but they are
legacy comparison artifacts rather than the source of truth. Correctness is now defined by
the theory theorems, not by smoke tests or by matching a particular backend iteration order.
