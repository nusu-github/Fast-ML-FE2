# Fast-ML-FE2 Estimator Design

**Date:** 2026-03-24
**Status:** Approved

## Overview

A high-performance foreground estimation implementation (Numba CPU + CuPy GPU) for the `fastmlfe2_eval` package. Exploits Lean-proven properties for aggressive optimizations: red-black Gauss-Seidel on CPU, shared-memory tiling and fused kernels on GPU, binary-pixel skip, and paper-optimal default parameters.

## Architecture

```
evaluation/src/fastmlfe2_eval/estimator/
├── __init__.py      # Public API + backend dispatch
├── _types.py        # Shared dataclass for parameters, level schedule computation
├── _cpu.py          # Numba: red-black Gauss-Seidel, binary skip
├── _gpu.py          # CuPy: shared-memory tiling, fused resize+iterate kernels
```

## Public API

```python
def estimate_foreground(
    image: NDArray[np.floating],       # h×w×3, [0,1]
    alpha: NDArray[np.floating],       # h×w, [0,1]
    *,
    regularization: float = 5e-3,      # ε (paper-optimal)
    gradient_weight: float = 0.1,      # ω (paper-optimal)
    n_small_iterations: int = 10,
    n_big_iterations: int = 2,
    small_size: int = 32,
    backend: str = "auto",             # "auto" | "cpu" | "gpu"
    return_background: bool = False,
) -> NDArray[np.float32] | tuple[NDArray[np.float32], NDArray[np.float32]]
```

- `backend="auto"` detects CuPy availability; falls back to Numba.
- Default parameters differ from pymatting (ε=1e-5, ω=1.0) based on the paper's Section 5.4 parameter study.

## Core Algorithm

### Multi-level scheme

Identical structure to pymatting/Germer et al. 2020:

- `n_levels = ceil(log2(max(w, h)))`
- Level sizes: `round(w0^(l/n_levels)) × round(h0^(l/n_levels))` for l = 0..n_levels
- Initialize F/B at 1×1 with weighted mean foreground/background color
- 10 iterations at levels ≤ 32×32, 2 iterations at larger levels

### Per-pixel 2×2 system

From Lean theorems `closedFormSolution` and `closedForm_solvesNormalEquation`:

```
w_j = ε + ω|α_i - α_j|    (neighbor weight, proven positive: neighborWeight_pos)
W = Σ_j w_j                (total weight, proven positive: totalWeight_pos)

A = [α² + W,    α(1-α) ]    b = [α·I + Σ w_j·F_j]
    [α(1-α), (1-α)² + W]        [(1-α)·I + Σ w_j·B_j]

det = (α² + W)·((1-α)² + W) - α²(1-α)²   (proven > 0: normalMatrix_det_pos)

F = ((1-α)² + W)·b_F - α(1-α)·b_B) / det
B = ((α² + W)·b_B - α(1-α)·b_F) / det
clamp to [0,1]
```

Matrix A is identical for all 3 RGB channels — compute det and inverse coefficients once, apply to all channels.

## Optimizations

### 1. Binary pixel skip

**Lean basis:** `jacobiSpectralRadius_eq_zero_of_alpha_zero`, `jacobiSpectralRadius_eq_zero_of_alpha_one`

When α < 0.01 or α > 0.99, spectral radius is ≈0, so the solution is (near-)exact in one step:
- α ≈ 0: F = weighted neighbor mean, B = image pixel
- α ≈ 1: F = image pixel, B = weighted neighbor mean

Both CPU and GPU kernels check this condition and skip the 2×2 solve.

### 2. Red-black Gauss-Seidel (CPU only)

Checkerboard coloring: red at `(x+y) % 2 == 0`, black at `== 1`.

Each iteration consists of two half-sweeps:
1. Update all red pixels (using current black neighbors)
2. Update all black pixels (using freshly updated red neighbors)

Within each color, pixels are independent → parallelizable with `prange`. Converges ~2× faster per iteration than pure Jacobi.

### 3. Double-buffered Jacobi (GPU)

Standard Jacobi iteration with `F_prev`/`F` buffer swap after each iteration. All pixels update in parallel from previous iteration's values. Justified by per-pixel independence (`jacobiStep` proven in `Level/Jacobi.lean`).

### 4. Shared-memory tiling (GPU)

Each CUDA thread block:
1. Loads a 32×32 tile + 1-pixel halo (34×34) of F_prev, B_prev, alpha into shared memory
2. Synchronizes
3. Computes the 4-neighbor accumulation from shared memory
4. Writes result to global F, B

Reduces global memory bandwidth ~4× for the neighbor accumulation phase.

### 5. Fused resize + first iteration (GPU)

A single kernel combines nearest-neighbor upsampling from the previous level with the first Jacobi iteration:
- Thread at (x,y) computes source coordinates in the previous level
- Reads F_prev, B_prev from previous-level buffers (nearest-neighbor)
- Reads image, alpha from current-level buffers (pre-resized)
- Computes one Jacobi step immediately
- Writes to current-level F, B

Eliminates one full-image memory round-trip per level.

### 6. Pre-allocated buffer pool

- CPU: Allocate F, B, F_work, B_work at max level size once
- GPU: Allocate F, B, F_prev, B_prev, image_level, alpha_level at max size once
- Reuse via slicing/views across all levels
- Avoids per-level allocation overhead (significant on GPU)

## Data Flow

```
estimate_foreground(image, alpha, backend="auto")
│
├─ Validate inputs: shape, dtype, range
├─ Compute level schedule: [(w_l, h_l, n_iter_l) for l in 0..n_levels]
├─ Compute initial F/B mean colors (vectorized)
│
├─ backend == "cpu"?
│   └─ _cpu.estimate_fb_ml(...)
│       ├─ Pre-allocate buffers (max level size)
│       └─ For each level:
│           ├─ _resize_nearest (prange)
│           └─ For each iteration:
│               ├─ _update_red_pixels(...)   # prange, binary skip
│               └─ _update_black_pixels(...)  # prange, binary skip
│
└─ backend == "gpu"?
    └─ _gpu.estimate_fb_ml(...)
        ├─ Upload to device (or accept cp.ndarray)
        ├─ Pre-allocate device buffers (max size)
        └─ For each level:
            ├─ First iteration: _fused_resize_iterate kernel
            ├─ Remaining iterations: _iterate_tiled kernel
            └─ Swap F ↔ F_prev, B ↔ B_prev
```

## Error Handling

- `ValueError` for wrong shapes (image.ndim != 3, alpha.ndim != 2, mismatch)
- `ValueError` if channels != 3 (GPU kernels hardcode depth=3)
- `RuntimeError` if backend="gpu" but CuPy unavailable
- No silent fallback — explicit backend prevents surprising performance cliffs

## Memory Budget (float32, worst case)

- **CPU:** 2 × h × w × 3 × 4 bytes (F/B) + same for work buffers ≈ 96 MB at 4K
- **GPU:** Same + image + alpha on device ≈ 120 MB at 4K

## Testing Strategy

Property-based validation derived from Lean theorems:

| Test | Lean theorem | Check |
|------|-------------|-------|
| Output in [0,1] | `closedForm_mem_box_of_exists_boxed_solution` | `(0 <= F).all() and (F <= 1).all()` |
| Compositing bound | `abs_compose_sub_compose_le_authored` | `\|α·F+(1-α)·B - I\|` bounded |
| Convergence monotone | `jacobiIterate_error_le` | Error decreases with more iterations |
| Fixed-point stability | `jacobiStep_closedFormSolution` | Re-running on converged output ≈ identity |
| Binary α exact | `jacobiSpectralRadius_eq_zero_of_alpha_*` | α∈{0,1} → F or B = image |
| Determinant positive | `normalMatrix_det_pos` | No NaN/Inf in output for valid input |
| CPU/GPU agreement | (both implement same math) | `np.allclose(cpu, gpu, atol=1e-4)` |

### Synthetic test fixtures

- Solid color + linear alpha gradient
- Checkerboard pattern (stress-tests red-black ordering)
- Random noise (fuzz)
- Single-pixel / 1×1 image (degenerate)
- All-zero and all-one alpha (pure binary)
- Known ground-truth composited image → SAD/MSE/GRAD regression

## References

- Germer et al. 2020, "Multilevel Foreground Estimation"
- Lean proofs: `FastMLFE2/Theorems/` (ClosedForm, JacobiContraction, Conditioning, MeanResidualBounds, CompositingError, NearBinary)
- pymatting reference: `estimate_foreground_ml.py`, `estimate_foreground_ml_cupy.py`
