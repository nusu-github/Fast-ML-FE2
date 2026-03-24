# Fast-ML-FE2 Evaluation

Evaluation harness for the proof implementations in [Fast-ML-FE2](../).

Computes error metrics (SAD, MSE, GRAD) that correspond to the quantities
formalized in the Lean proofs, against reference foreground estimation results.

Originally derived from [pymatting/foreground-estimation-evaluation](https://github.com/pymatting/foreground-estimation-evaluation).

## Setup

```bash
uv sync
```

## Usage

```python
from fastmlfe2_eval import sad_error, mse_error, gradient_error
```

## References

Christoph Rhemann, Carsten Rother, Jue Wang, Margrit Gelautz, Pushmeet Kohli, Pamela Rott.
*A Perceptually Motivated Online Benchmark for Image Matting.*
CVPR, June 2009.
