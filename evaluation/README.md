# Fast-ML-FE2 Evaluation

Evaluation harness for the proof implementations in [Fast-ML-FE2](../).

Computes error metrics (SAD, MSE, GRAD) that correspond to the quantities
formalized in the Lean proofs, against reference foreground estimation results.
For GRAD, the Lean canonical semantics matches the default Python kernel
configuration `sigma = 1.4`.

The package also provides Lean-backed synthetic pattern families for theorem-led
metric tests and backend benchmarks:

- `saturating_slab` for SAD/MSE near-supremum cases
- `centered_vertical_step` for GRAD edge-vs-flat cases
- `shifted_vertical_step_pair` for GRAD shifted-edge cases
- `checkerboard` for high-frequency GRAD-positive cases

Originally derived from [pymatting/foreground-estimation-evaluation](https://github.com/pymatting/foreground-estimation-evaluation).

## Setup

```bash
uv sync
```

## Usage

```python
from fastmlfe2_eval import (
    gradient_error,
    list_pattern_families,
    make_pattern_case,
    mse_error,
    sad_error,
)

case = make_pattern_case("centered_vertical_step", 128, 128)
grad = gradient_error(case.probe_fg, case.reference_fg, case.weights, case.mask)
families = list_pattern_families()
```

`mse_error` intentionally follows the Python implementation semantics
(weighted mean on the masked region), while the Lean paper-theory layer keeps
the weighted-sum form separate. `gradient_error` matches the discrete canonical
Lean semantics at the default kernel configuration.

## References

Christoph Rhemann, Carsten Rother, Jue Wang, Margrit Gelautz, Pushmeet Kohli, Pamela Rott.
*A Perceptually Motivated Online Benchmark for Image Matting.*
CVPR, June 2009.
