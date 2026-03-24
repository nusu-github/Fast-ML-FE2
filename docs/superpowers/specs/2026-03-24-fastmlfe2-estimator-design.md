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
- **Parameter mapping:** `gradient_weight` in the API corresponds to `omega` (ω) in the Lean formalization and the paper. `regularization` corresponds to `epsilonR` (ε).
- Inputs are cast to `float32` and made contiguous (`np.ascontiguousarray`) before dispatching to backends.

## Core Algorithm

### Multi-level scheme

Identical structure to pymatting/Germer et al. 2020:

- `n_levels = ceil(log2(max(w, h)))`
- Level sizes: `round(w0^(l/n_levels)) × round(h0^(l/n_levels))` for l = 0..n_levels
- Initialize F/B at 1×1 with weighted mean foreground/background color (vectorized over all pixels; pymatting CuPy reference instead resizes the image to 1×1 — we follow the CPU reference which is more principled)
- 10 iterations at levels where `w <= small_size and h <= small_size`, 2 iterations otherwise (follows pymatting CPU semantics; the CuPy reference uses `min(w,h) <= small_size` which is a bug)

### Per-pixel solve: mean-residual correction form

From Lean theorem `meanResidualSolution_eq_closedFormSolution` (H5), which proves equivalence to the Cramer-form closed-form solution while requiring fewer operations per channel:

```
w_j = ε + ω|α_i - α_j|              (neighbor weight, proven positive: neighborWeight_pos)
W = Σ_j w_j                          (total weight, proven positive: totalWeight_pos)

λ_j = w_j / W                        (normalized weight, sum = 1: sum_normalizedWeight_eq_one)
μ_F^c = Σ_j λ_j · F_j^c             (weighted foreground mean)
μ_B^c = Σ_j λ_j · B_j^c             (weighted background mean)
D = W + α² + (1-α)²                  (weightedMeanDenom, proven > 0: weightedMeanDenom_pos)
r^c = I^c - α·μ_F^c - (1-α)·μ_B^c   (mean residual, proven |r| ≤ 1: abs_meanResidual_le_one_of_boxed_inputs)
inv_D = 1 / D                        (shared across 3 channels)

F^c = clamp(μ_F^c + α · r^c · inv_D, 0, 1)       (per channel)
B^c = clamp(μ_B^c + (1-α) · r^c · inv_D, 0, 1)   (per channel)
```

**Why mean-residual over Cramer form:**
- Neighbor accumulation computes `μ_F`, `μ_B` (weighted means) instead of raw sums, naturally normalized
- `D = W + α² + (1-α)²` is 2 additions vs Cramer's `det = (α²+W)·((1-α)²+W) - α²(1-α)²` (2 mul + 1 sub)
- `r` is a single scalar per channel; correction `α·r/D` reuses `α/D` across channels
- On GPU, `r` fits in a register per channel — no need to store intermediate 2×2 inverse coefficients
- Directly exposes the structure: solution = mean + small correction (proven bounded by H10)

**Binary-α special cases** (from `meanResidualSolution_*_of_alpha_zero/one`):
- α = 0: F = μ_F, B = μ_B + r/(W+1)
- α = 1: F = μ_F + r/(W+1), B = μ_B

## Optimizations

### 1. Binary pixel skip

**Lean basis (strict):** `jacobiSpectralRadius_eq_zero_of_alpha_zero`, `jacobiSpectralRadius_eq_zero_of_alpha_one` — at α ∈ {0,1} the spectral radius is exactly 0, so the solution is exact in one step.

**Lean basis (soft threshold):** `abs_foreground_correction_le` (H10) proves |α·r/D| ≤ 2α. For α < 0.01, the correction term is at most 0.02, which is below 1/255 (uint8 quantization threshold) and thus invisible in the final output. Symmetrically, |(1-α)·r/D| ≤ 2(1-α) for the background correction near α = 1.

**Implementation:** When α < 0.01 or α > 0.99, use the binary-α special case from the mean-residual form:
- α ≈ 0: F = μ_F, B = μ_B + r/(W+1)
- α ≈ 1: F = μ_F + r/(W+1), B = μ_B

Both CPU and GPU kernels check this condition and skip the full solve.

### 2. Red-black Gauss-Seidel (CPU only)

Checkerboard coloring: red at `(x+y) % 2 == 0`, black at `== 1`.

Each iteration consists of two half-sweeps:
1. Update all red pixels (using current black neighbors)
2. Update all black pixels (using freshly updated red neighbors)

Within each color, pixels are independent → parallelizable with `prange`. Empirically converges ~2× faster per iteration than pure Jacobi. Note: the current Lean theory layer formalizes only Jacobi contraction (H6); red-black Gauss-Seidel convergence is not formally verified. The speed advantage is well-established in numerical PDE literature but is not backed by a project-specific proof.

### 3. Double-buffered Jacobi (GPU)

Standard Jacobi iteration with `F_prev`/`F` buffer swap after each iteration. All pixels update in parallel from previous iteration's values. Justified by per-pixel independence (`jacobiStep` proven in `Level/Jacobi.lean`).

### 4. Shared-memory tiling (GPU)

Each CUDA thread block:
1. Loads a 32×32 tile + 1-pixel halo (34×34) of F_prev, B_prev, alpha into shared memory
2. Synchronizes
3. Computes the 4-neighbor accumulation from shared memory
4. Writes result to global F, B

Shared memory per block: 34×34 × (3+3+1) × 4 bytes = ~32 KB (within 48 KB limit).
Reduces global memory bandwidth ~4× for the neighbor accumulation phase.

With the mean-residual form, the per-thread computation accumulates `μ_F`, `μ_B` from shared memory neighbors, then computes `r` and the correction `α·r·inv_D` in registers. The intermediate quantities `r`, `inv_D`, `α/D` are scalars or per-channel registers — no shared-memory storage needed beyond F_prev, B_prev, alpha.

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

## Memory Budget (float32, worst case at 4K = 3840×2160)

- **CPU:** F + B + F_work + B_work = 4 × 3840 × 2160 × 3 × 4 ≈ 398 MB
- **GPU:** F + B + F_prev + B_prev + image + alpha = (5 × 3 + 1) × 3840 × 2160 × 4 ≈ 530 MB

Note: pymatting CuPy reference has similar budget. Levels below full resolution reuse the same buffers via slicing.

## Testing Strategy

Property-based validation derived from Lean theorems:

| Test | Lean theorem | Check |
|------|-------------|-------|
| Output in [0,1] | `closedForm_mem_box_of_exists_boxed_solution` | `(0 <= F).all() and (F <= 1).all()` |
| Compositing bound | `abs_compose_sub_compose_le_authored` | `\|α·F+(1-α)·B - I\|` bounded |
| Convergence monotone (GPU) | `jacobiIterate_error_le` | Error decreases with more iterations (Jacobi) |
| Convergence monotone (CPU) | *(empirical, no formal proof)* | Error decreases with more iterations (red-black GS) |
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

## Pymatting Reference Divergences

The following discrepancies in the pymatting CuPy reference (`estimate_foreground_ml_cupy.py`) are intentionally not carried forward:

1. **Missing `gradient_weight`**: The CuPy kernel uses `fabsf(a0 - alpha[j])` without the ω multiplier. The CPU version correctly uses `regularization + gradient_weight * gradient`. Our implementation applies ω consistently in both backends.
2. **Small-size threshold**: CuPy uses `min(w,h) <= small_size`, CPU uses `w <= small_size and h <= small_size`. We follow the CPU (both dimensions must be small).
3. **Initialization**: CuPy resizes the full image to 1×1 for initial F/B. CPU computes weighted mean over α>0.9 / α<0.1 pixels. We follow the CPU approach.

## References

- Germer et al. 2020, "Multilevel Foreground Estimation"
- Lean proofs: `FastMLFE2/Theorems/` (ClosedForm, JacobiContraction, Conditioning, MeanResidualBounds, CompositingError, NearBinary)
- pymatting reference: `estimate_foreground_ml.py`, `estimate_foreground_ml_cupy.py`
