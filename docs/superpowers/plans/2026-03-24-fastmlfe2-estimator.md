# Fast-ML-FE2 Estimator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement high-performance multi-level foreground estimation with Numba CPU (red-black Gauss-Seidel) and CuPy GPU (Jacobi with shared-memory tiling) backends, using the mean-residual correction form proven in Lean.

**Architecture:** Subpackage `fastmlfe2_eval.estimator` with 4 modules: `_types.py` (params/schedule), `_cpu.py` (Numba red-black GS), `_gpu.py` (CuPy Jacobi), `__init__.py` (API/dispatch). Both backends use the mean-residual form (H5) with binary pixel skip (H10).

**Tech Stack:** Python 3.13+, NumPy 2+, Numba 0.64+, CuPy 14+ (CUDA 12), pytest 8+

**Spec:** `docs/superpowers/specs/2026-03-24-fastmlfe2-estimator-design.md`

---

### File Structure

| Action | Path | Responsibility |
|--------|------|---------------|
| Create | `evaluation/src/fastmlfe2_eval/estimator/__init__.py` | Public API, backend dispatch, input validation |
| Create | `evaluation/src/fastmlfe2_eval/estimator/_types.py` | EstimatorParams, LevelSpec, compute_level_schedule, compute_initial_means |
| Create | `evaluation/src/fastmlfe2_eval/estimator/_cpu.py` | Numba resize, red-black GS mean-residual kernel, multi-level loop |
| Create | `evaluation/src/fastmlfe2_eval/estimator/_gpu.py` | CuPy resize kernel, iteration kernels (basic → tiled → fused), multi-level loop |
| Modify | `evaluation/src/fastmlfe2_eval/__init__.py` | Re-export estimate_foreground |
| Create | `evaluation/tests/test_types.py` | Unit tests for _types.py |
| Create | `evaluation/tests/test_estimator_cpu.py` | CPU kernel correctness + property tests |
| Create | `evaluation/tests/test_estimator_gpu.py` | GPU property tests + CPU/GPU agreement |

---

### Task 1: Types Module

**Files:**
- Create: `evaluation/src/fastmlfe2_eval/estimator/_types.py`
- Create: `evaluation/tests/test_types.py`

- [ ] **Step 1: Write test_types.py**

```python
import numpy as np
import pytest

from fastmlfe2_eval.estimator._types import (
    EstimatorParams,
    compute_initial_means,
    compute_level_schedule,
)


def test_schedule_endpoints():
    schedule = compute_level_schedule(64, 32, EstimatorParams())
    assert schedule[0].w == 1 and schedule[0].h == 1
    assert schedule[-1].w == 64 and schedule[-1].h == 32


def test_schedule_monotone_growth():
    schedule = compute_level_schedule(640, 480, EstimatorParams())
    for i in range(1, len(schedule)):
        assert schedule[i].w >= schedule[i - 1].w
        assert schedule[i].h >= schedule[i - 1].h


def test_schedule_small_vs_big_iterations():
    params = EstimatorParams(n_small_iterations=10, n_big_iterations=2, small_size=32)
    schedule = compute_level_schedule(256, 256, params)
    for lvl in schedule:
        if lvl.w <= 32 and lvl.h <= 32:
            assert lvl.n_iter == 10
        else:
            assert lvl.n_iter == 2


def test_schedule_max_growth_factor():
    """Adjacent levels should grow by at most ~2x in each dimension."""
    schedule = compute_level_schedule(1024, 768, EstimatorParams())
    for i in range(1, len(schedule)):
        assert schedule[i].w <= 2 * schedule[i - 1].w + 1
        assert schedule[i].h <= 2 * schedule[i - 1].h + 1


def test_initial_means_pure_foreground():
    image = np.full((4, 4, 3), 0.5, dtype=np.float32)
    alpha = np.ones((4, 4), dtype=np.float32)
    fg, bg = compute_initial_means(image, alpha)
    np.testing.assert_allclose(fg, [0.5, 0.5, 0.5])
    np.testing.assert_allclose(bg, [0.0, 0.0, 0.0])


def test_initial_means_pure_background():
    image = np.full((4, 4, 3), 0.7, dtype=np.float32)
    alpha = np.zeros((4, 4), dtype=np.float32)
    fg, bg = compute_initial_means(image, alpha)
    np.testing.assert_allclose(fg, [0.0, 0.0, 0.0])
    np.testing.assert_allclose(bg, [0.7, 0.7, 0.7])


def test_initial_means_mixed():
    rng = np.random.default_rng(42)
    image = rng.random((16, 16, 3)).astype(np.float32)
    alpha = rng.random((16, 16)).astype(np.float32)
    fg, bg = compute_initial_means(image, alpha)
    assert fg.shape == (3,) and fg.dtype == np.float32
    assert bg.shape == (3,) and bg.dtype == np.float32


def test_schedule_1x1_image():
    """Edge case: 1×1 image should produce exactly 1 level."""
    schedule = compute_level_schedule(1, 1, EstimatorParams())
    assert len(schedule) == 1
    assert schedule[0].w == 1 and schedule[0].h == 1
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_types.py -v`
Expected: FAIL (ModuleNotFoundError)

- [ ] **Step 3: Implement _types.py**

```python
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from numpy.typing import NDArray


@dataclass(frozen=True, slots=True)
class EstimatorParams:
    regularization: float = 5e-3
    gradient_weight: float = 0.1
    n_small_iterations: int = 10
    n_big_iterations: int = 2
    small_size: int = 32


@dataclass(frozen=True, slots=True)
class LevelSpec:
    w: int
    h: int
    n_iter: int


def compute_level_schedule(w0: int, h0: int, params: EstimatorParams) -> list[LevelSpec]:
    if w0 <= 1 and h0 <= 1:
        n_iter = params.n_small_iterations
        return [LevelSpec(w=1, h=1, n_iter=n_iter)]

    n_levels = math.ceil(math.log2(max(w0, h0)))
    schedule: list[LevelSpec] = []
    for i_level in range(n_levels + 1):
        w = round(w0 ** (i_level / n_levels))
        h = round(h0 ** (i_level / n_levels))
        if w <= params.small_size and h <= params.small_size:
            n_iter = params.n_small_iterations
        else:
            n_iter = params.n_big_iterations
        schedule.append(LevelSpec(w=w, h=h, n_iter=n_iter))
    return schedule


def compute_initial_means(
    image: NDArray[np.float32], alpha: NDArray[np.float32]
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    fg_mask = alpha > 0.9
    bg_mask = alpha < 0.1
    fg_count = int(fg_mask.sum())
    bg_count = int(bg_mask.sum())
    if fg_count > 0:
        fg_mean = image[fg_mask].mean(axis=0).astype(np.float32)
    else:
        fg_mean = np.zeros(3, dtype=np.float32)
    if bg_count > 0:
        bg_mean = image[bg_mask].mean(axis=0).astype(np.float32)
    else:
        bg_mean = np.zeros(3, dtype=np.float32)
    return fg_mean, bg_mean
```

- [ ] **Step 4: Create `__init__.py` stub for the estimator subpackage**

Create empty `evaluation/src/fastmlfe2_eval/estimator/__init__.py`:

```python
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_types.py -v`
Expected: all PASS

- [ ] **Step 6: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add src/fastmlfe2_eval/estimator/__init__.py src/fastmlfe2_eval/estimator/_types.py tests/test_types.py
git commit -m "feat(estimator): add types module with params, level schedule, initial means"
```

---

### Task 2: CPU Backend

**Files:**
- Create: `evaluation/src/fastmlfe2_eval/estimator/_cpu.py`
- Create: `evaluation/tests/test_estimator_cpu.py` (kernel correctness only)

- [ ] **Step 1: Write kernel correctness test**

Hand-computed reference for a 3×3 image with uniform α=0.5, ε=0.1, ω=0.0:
- Center pixel (1,1): 4 neighbors, all w_j = ε = 0.1, W = 0.4
- μ_F = 0.6 (all neighbors), μ_B = 0.3, image = 0.8
- D = 0.4 + 0.25 + 0.25 = 0.9
- r = 0.8 - 0.5×0.6 - 0.5×0.3 = 0.35
- F = 0.6 + 0.5 × 0.35/0.9 ≈ 0.7944
- B = 0.3 + 0.5 × 0.35/0.9 ≈ 0.4944

```python
import numpy as np
import pytest

from fastmlfe2_eval.estimator._cpu import _resize_nearest, _resize_nearest_multichannel, _update_rb_half


class TestResizeNearest:
    def test_identity(self):
        src = np.random.default_rng(0).random((4, 4, 3)).astype(np.float32)
        dst = np.empty_like(src)
        _resize_nearest_multichannel(dst, src)
        np.testing.assert_array_equal(dst, src)

    def test_upsample_2x(self):
        src = np.array([[[1.0, 0.0, 0.0]]], dtype=np.float32)  # 1×1
        dst = np.empty((2, 2, 3), dtype=np.float32)
        _resize_nearest_multichannel(dst, src)
        np.testing.assert_array_equal(dst, np.full((2, 2, 3), [[1.0, 0.0, 0.0]], dtype=np.float32))

    def test_downsample(self):
        src = np.arange(16, dtype=np.float32).reshape(4, 4)
        dst = np.empty((2, 2), dtype=np.float32)
        _resize_nearest(dst, src)
        assert dst.shape == (2, 2)

    def test_1x1(self):
        src = np.ones((8, 8, 3), dtype=np.float32)
        dst = np.empty((1, 1, 3), dtype=np.float32)
        _resize_nearest_multichannel(dst, src)
        np.testing.assert_array_equal(dst[0, 0], [1.0, 1.0, 1.0])


class TestMeanResidualKernel:
    def test_center_pixel_uniform_alpha(self):
        """Hand-computed: 3×3, α=0.5 everywhere, ε=0.1, ω=0.0."""
        h, w = 3, 3
        F = np.full((h, w, 3), 0.6, dtype=np.float32)
        B = np.full((h, w, 3), 0.3, dtype=np.float32)
        image = np.full((h, w, 3), 0.8, dtype=np.float32)
        alpha = np.full((h, w), 0.5, dtype=np.float32)

        _update_rb_half(F, B, image, alpha, h, w, 0.1, 0.0, 0)  # red

        expected_F = 0.6 + 0.5 * 0.35 / 0.9
        expected_B = 0.3 + 0.5 * 0.35 / 0.9
        np.testing.assert_allclose(F[1, 1, 0], expected_F, atol=1e-6)
        np.testing.assert_allclose(B[1, 1, 0], expected_B, atol=1e-6)

    def test_binary_skip_alpha_zero(self):
        """α=0 everywhere: F should be neighbor mean, B gets correction."""
        h, w = 3, 3
        F = np.full((h, w, 3), 0.5, dtype=np.float32)
        B = np.full((h, w, 3), 0.3, dtype=np.float32)
        image = np.full((h, w, 3), 0.7, dtype=np.float32)
        alpha = np.zeros((h, w), dtype=np.float32)

        _update_rb_half(F, B, image, alpha, h, w, 0.1, 0.0, 0)

        # α=0: F = μ_F = 0.5, B = μ_B + r/(W+1)
        # W = 4*0.1 = 0.4, r = 0.7 - 0*0.5 - 1*0.3 = 0.4
        # B = 0.3 + 0.4/1.4 ≈ 0.5857
        np.testing.assert_allclose(F[1, 1, 0], 0.5, atol=1e-6)
        np.testing.assert_allclose(B[1, 1, 0], 0.3 + 0.4 / 1.4, atol=1e-5)

    def test_binary_skip_alpha_one(self):
        """α=1 everywhere: B should be neighbor mean, F gets correction."""
        h, w = 3, 3
        F = np.full((h, w, 3), 0.5, dtype=np.float32)
        B = np.full((h, w, 3), 0.3, dtype=np.float32)
        image = np.full((h, w, 3), 0.7, dtype=np.float32)
        alpha = np.ones((h, w), dtype=np.float32)

        _update_rb_half(F, B, image, alpha, h, w, 0.1, 0.0, 0)

        # α=1: B = μ_B = 0.3, F = μ_F + r/(W+1)
        # r = 0.7 - 1*0.5 - 0*0.3 = 0.2
        # F = 0.5 + 0.2/1.4 ≈ 0.6429
        np.testing.assert_allclose(B[1, 1, 0], 0.3, atol=1e-6)
        np.testing.assert_allclose(F[1, 1, 0], 0.5 + 0.2 / 1.4, atol=1e-5)

    def test_red_black_independence(self):
        """Red sweep should not modify black pixels and vice versa."""
        rng = np.random.default_rng(42)
        h, w = 8, 8
        F = rng.random((h, w, 3)).astype(np.float32)
        B = rng.random((h, w, 3)).astype(np.float32)
        image = rng.random((h, w, 3)).astype(np.float32)
        alpha = rng.random((h, w)).astype(np.float32)

        F_before = F.copy()
        _update_rb_half(F, B, image, alpha, h, w, 5e-3, 0.1, 0)  # red only

        # Black pixels should be unchanged
        for y in range(h):
            for x in range(w):
                if (x + y) % 2 == 1:  # black
                    np.testing.assert_array_equal(F[y, x], F_before[y, x])

    def test_output_bounded_01(self):
        """Output should always be in [0, 1] regardless of input."""
        rng = np.random.default_rng(99)
        h, w = 16, 16
        F = rng.random((h, w, 3)).astype(np.float32)
        B = rng.random((h, w, 3)).astype(np.float32)
        image = rng.random((h, w, 3)).astype(np.float32)
        alpha = rng.random((h, w)).astype(np.float32)

        _update_rb_half(F, B, image, alpha, h, w, 5e-3, 0.1, 0)
        _update_rb_half(F, B, image, alpha, h, w, 5e-3, 0.1, 1)

        assert np.all(F >= 0.0) and np.all(F <= 1.0)
        assert np.all(B >= 0.0) and np.all(B <= 1.0)
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_estimator_cpu.py -v`
Expected: FAIL (ImportError)

- [ ] **Step 3: Implement _cpu.py**

```python
from __future__ import annotations

import numpy as np
from numba import njit, prange

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from numpy.typing import NDArray
    from fastmlfe2_eval.estimator._types import EstimatorParams

from fastmlfe2_eval.estimator._types import compute_initial_means, compute_level_schedule


@njit("void(f4[:,:,:], f4[:,:,:])", cache=True, nogil=True, parallel=True)
def _resize_nearest_multichannel(dst, src):
    h_src, w_src, depth = src.shape
    h_dst, w_dst, depth = dst.shape
    for y_dst in prange(h_dst):
        for x_dst in range(w_dst):
            x_src = max(0, min(w_src - 1, x_dst * w_src // w_dst))
            y_src = max(0, min(h_src - 1, y_dst * h_src // h_dst))
            for c in range(depth):
                dst[y_dst, x_dst, c] = src[y_src, x_src, c]


@njit("void(f4[:,:], f4[:,:])", cache=True, nogil=True, parallel=True)
def _resize_nearest(dst, src):
    h_src, w_src = src.shape
    h_dst, w_dst = dst.shape
    for y_dst in prange(h_dst):
        for x_dst in range(w_dst):
            x_src = max(0, min(w_src - 1, x_dst * w_src // w_dst))
            y_src = max(0, min(h_src - 1, y_dst * h_src // h_dst))
            dst[y_dst, x_dst] = src[y_src, x_src]


@njit(cache=True, nogil=True, parallel=True)
def _update_rb_half(F, B, image, alpha, h, w, eps, omega, color):
    """Red-black Gauss-Seidel half-sweep using mean-residual correction form.

    Updates pixels where (x + y) % 2 == color.
    Within each color, pixels are independent (safe for prange).
    """
    dx = [-1, 1, 0, 0]
    dy = [0, 0, -1, 1]

    for y in prange(h):
        x_start = (color + y) % 2
        for x in range(x_start, w, 2):
            a0 = alpha[y, x]
            a1 = 1.0 - a0

            # Neighbor accumulation
            W = 0.0
            sum_wF = np.zeros(3, dtype=np.float32)
            sum_wB = np.zeros(3, dtype=np.float32)

            for d in range(4):
                x2 = max(0, min(w - 1, x + dx[d]))
                y2 = max(0, min(h - 1, y + dy[d]))
                wj = eps + omega * abs(a0 - alpha[y2, x2])
                W += wj
                for c in range(3):
                    sum_wF[c] += wj * F[y2, x2, c]
                    sum_wB[c] += wj * B[y2, x2, c]

            inv_W = 1.0 / W

            # Binary pixel skip (H10: |α·r/D| ≤ 2α, sub-quantization for α < 0.01)
            if a0 < 0.01 or a0 > 0.99:
                inv_Wp1 = 1.0 / (W + 1.0)
                for c in range(3):
                    mu_F = sum_wF[c] * inv_W
                    mu_B = sum_wB[c] * inv_W
                    r = image[y, x, c] - a0 * mu_F - a1 * mu_B
                    if a0 < 0.01:
                        F[y, x, c] = max(0.0, min(1.0, mu_F))
                        B[y, x, c] = max(0.0, min(1.0, mu_B + r * inv_Wp1))
                    else:
                        F[y, x, c] = max(0.0, min(1.0, mu_F + r * inv_Wp1))
                        B[y, x, c] = max(0.0, min(1.0, mu_B))
                continue

            # General case: mean-residual correction (H5)
            D = W + a0 * a0 + a1 * a1
            inv_D = 1.0 / D
            a0_inv_D = a0 * inv_D
            a1_inv_D = a1 * inv_D

            for c in range(3):
                mu_F = sum_wF[c] * inv_W
                mu_B = sum_wB[c] * inv_W
                r = image[y, x, c] - a0 * mu_F - a1 * mu_B
                F[y, x, c] = max(0.0, min(1.0, mu_F + a0_inv_D * r))
                B[y, x, c] = max(0.0, min(1.0, mu_B + a1_inv_D * r))


def estimate_fb_ml(
    input_image: NDArray[np.float32],
    input_alpha: NDArray[np.float32],
    params: EstimatorParams,
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    h0, w0, _depth = input_image.shape
    schedule = compute_level_schedule(w0, h0, params)
    fg_mean, bg_mean = compute_initial_means(input_image, input_alpha)

    F_prev = np.empty((1, 1, 3), dtype=np.float32)
    B_prev = np.empty((1, 1, 3), dtype=np.float32)
    F_prev[0, 0, :] = fg_mean
    B_prev[0, 0, :] = bg_mean

    eps = np.float32(params.regularization)
    omega = np.float32(params.gradient_weight)

    for level in schedule:
        w, h, n_iter = level.w, level.h, level.n_iter

        image = np.empty((h, w, 3), dtype=np.float32)
        alpha = np.empty((h, w), dtype=np.float32)
        F = np.empty((h, w, 3), dtype=np.float32)
        B = np.empty((h, w, 3), dtype=np.float32)

        _resize_nearest_multichannel(image, input_image)
        _resize_nearest(alpha, input_alpha)
        _resize_nearest_multichannel(F, F_prev)
        _resize_nearest_multichannel(B, B_prev)

        for _i_iter in range(n_iter):
            _update_rb_half(F, B, image, alpha, h, w, eps, omega, 0)
            _update_rb_half(F, B, image, alpha, h, w, eps, omega, 1)

        F_prev = F
        B_prev = B

    return F_prev, B_prev
```

- [ ] **Step 4: Run tests**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_estimator_cpu.py -v`
Expected: all PASS

- [ ] **Step 5: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add src/fastmlfe2_eval/estimator/_cpu.py tests/test_estimator_cpu.py
git commit -m "feat(estimator): add CPU backend with red-black GS mean-residual kernel"
```

---

### Task 3: Public API + CPU Property Tests

**Files:**
- Modify: `evaluation/src/fastmlfe2_eval/estimator/__init__.py`
- Modify: `evaluation/src/fastmlfe2_eval/__init__.py`
- Modify: `evaluation/tests/test_estimator_cpu.py`

- [ ] **Step 1: Add property tests to test_estimator_cpu.py**

Append the following to the existing test file:

```python
from fastmlfe2_eval.estimator import estimate_foreground


def _make_composited(h=32, w=32, seed=42):
    """Create a composited image with known ground-truth F, B, alpha."""
    rng = np.random.default_rng(seed)
    F_true = rng.random((h, w, 3)).astype(np.float32)
    B_true = rng.random((h, w, 3)).astype(np.float32)
    alpha = rng.random((h, w)).astype(np.float32)
    image = (alpha[:, :, np.newaxis] * F_true + (1 - alpha[:, :, np.newaxis]) * B_true).astype(
        np.float32
    )
    return image, alpha, F_true, B_true


class TestCPUProperties:
    """Property-based tests derived from Lean theorems."""

    def test_output_in_01(self):
        """closedForm_mem_box_of_exists_boxed_solution"""
        image, alpha, _, _ = _make_composited()
        F, B = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        assert np.all(F >= 0.0) and np.all(F <= 1.0)
        assert np.all(B >= 0.0) and np.all(B <= 1.0)

    def test_no_nan_inf(self):
        """normalMatrix_det_pos: determinant > 0 implies no division by zero."""
        image, alpha, _, _ = _make_composited()
        F, B = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        assert np.all(np.isfinite(F))
        assert np.all(np.isfinite(B))

    def test_binary_alpha_zero(self):
        """α=0: F arbitrary, B ≈ image."""
        image = np.random.default_rng(0).random((16, 16, 3)).astype(np.float32)
        alpha = np.zeros((16, 16), dtype=np.float32)
        F, B = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        np.testing.assert_allclose(B, image, atol=0.05)

    def test_binary_alpha_one(self):
        """α=1: F ≈ image, B arbitrary."""
        image = np.random.default_rng(0).random((16, 16, 3)).astype(np.float32)
        alpha = np.ones((16, 16), dtype=np.float32)
        F = estimate_foreground(image, alpha, backend="cpu")
        np.testing.assert_allclose(F, image, atol=0.05)

    def test_compositing_residual_bounded(self):
        """abs_compose_sub_compose_le_authored: residual small in unknown region."""
        image, alpha, _, _ = _make_composited()
        F, B = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        composite = alpha[:, :, np.newaxis] * F + (1 - alpha[:, :, np.newaxis]) * B
        residual = np.abs(composite - image)
        # In transition region (0.1 < α < 0.9), residual should be small
        mask = (alpha > 0.1) & (alpha < 0.9)
        assert residual[mask].mean() < 0.1

    def test_fixed_point_stability(self):
        """jacobiStep_closedFormSolution: re-running on converged output ≈ identity."""
        image, alpha, _, _ = _make_composited()
        F1 = estimate_foreground(image, alpha, backend="cpu")
        F2 = estimate_foreground(image, alpha, backend="cpu")
        np.testing.assert_allclose(F1, F2, atol=1e-6)

    def test_convergence_monotone(self):
        """Empirical: error should decrease with more iterations."""
        image, alpha, F_true, _ = _make_composited()
        err_prev = np.inf
        for n_iter in [1, 2, 5, 10]:
            F = estimate_foreground(
                image, alpha, backend="cpu", n_small_iterations=n_iter, n_big_iterations=n_iter
            )
            err = np.mean(np.abs(F - F_true))
            assert err <= err_prev + 1e-6, f"Error increased at n_iter={n_iter}"
            err_prev = err

    def test_1x1_image(self):
        image = np.array([[[0.5, 0.3, 0.7]]], dtype=np.float32)
        alpha = np.array([[0.6]], dtype=np.float32)
        F, B = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        assert F.shape == (1, 1, 3)
        assert np.all(np.isfinite(F)) and np.all(np.isfinite(B))

    def test_checkerboard_alpha(self):
        """Stress test for red-black ordering."""
        h, w = 16, 16
        image = np.random.default_rng(1).random((h, w, 3)).astype(np.float32)
        alpha = np.zeros((h, w), dtype=np.float32)
        alpha[::2, ::2] = 1.0
        alpha[1::2, 1::2] = 1.0
        F = estimate_foreground(image, alpha, backend="cpu")
        assert np.all(np.isfinite(F))
        assert np.all(F >= 0.0) and np.all(F <= 1.0)

    def test_return_foreground_only(self):
        image, alpha, _, _ = _make_composited()
        result = estimate_foreground(image, alpha, backend="cpu", return_background=False)
        assert isinstance(result, np.ndarray)
        assert result.shape == image.shape

    def test_return_background(self):
        image, alpha, _, _ = _make_composited()
        result = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        assert isinstance(result, tuple) and len(result) == 2
```

- [ ] **Step 2: Implement estimator/__init__.py**

```python
from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

from fastmlfe2_eval.estimator._types import EstimatorParams

if TYPE_CHECKING:
    from numpy.typing import NDArray


def _detect_backend() -> str:
    try:
        import cupy  # noqa: F401

        return "gpu"
    except ImportError:
        return "cpu"


def estimate_foreground(
    image: NDArray[np.floating],
    alpha: NDArray[np.floating],
    *,
    regularization: float = 5e-3,
    gradient_weight: float = 0.1,
    n_small_iterations: int = 10,
    n_big_iterations: int = 2,
    small_size: int = 32,
    backend: str = "auto",
    return_background: bool = False,
) -> NDArray[np.float32] | tuple[NDArray[np.float32], NDArray[np.float32]]:
    if image.ndim != 3 or image.shape[2] != 3:
        msg = f"image must be h×w×3, got shape {image.shape}"
        raise ValueError(msg)
    if alpha.ndim != 2:
        msg = f"alpha must be h×w, got shape {alpha.shape}"
        raise ValueError(msg)
    if image.shape[:2] != alpha.shape:
        msg = f"shape mismatch: image {image.shape[:2]} vs alpha {alpha.shape}"
        raise ValueError(msg)

    image_f32 = np.ascontiguousarray(image, dtype=np.float32)
    alpha_f32 = np.ascontiguousarray(alpha, dtype=np.float32)

    params = EstimatorParams(
        regularization=regularization,
        gradient_weight=gradient_weight,
        n_small_iterations=n_small_iterations,
        n_big_iterations=n_big_iterations,
        small_size=small_size,
    )

    if backend == "auto":
        backend = _detect_backend()

    if backend == "cpu":
        from fastmlfe2_eval.estimator._cpu import estimate_fb_ml

        foreground, background = estimate_fb_ml(image_f32, alpha_f32, params)
    elif backend == "gpu":
        try:
            from fastmlfe2_eval.estimator._gpu import estimate_fb_ml
        except ImportError:
            msg = "backend='gpu' requires CuPy (pip install cupy-cuda12x)"
            raise RuntimeError(msg) from None

        foreground, background = estimate_fb_ml(image_f32, alpha_f32, params)
    else:
        msg = f"unknown backend: {backend!r}, expected 'auto', 'cpu', or 'gpu'"
        raise ValueError(msg)

    if return_background:
        return foreground, background
    return foreground
```

- [ ] **Step 3: Update package __init__.py**

Modify `evaluation/src/fastmlfe2_eval/__init__.py`:

```python
"""Evaluation harness for Fast-ML-FE2 proof implementations."""

from fastmlfe2_eval.estimator import estimate_foreground
from fastmlfe2_eval.metrics import gradient_error, mse_error, sad_error

__all__ = ["estimate_foreground", "sad_error", "mse_error", "gradient_error"]
```

- [ ] **Step 4: Run all tests**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_estimator_cpu.py tests/test_types.py tests/test_metrics.py -v`
Expected: all PASS

- [ ] **Step 5: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add src/fastmlfe2_eval/estimator/__init__.py src/fastmlfe2_eval/__init__.py tests/test_estimator_cpu.py
git commit -m "feat(estimator): add public API with CPU property tests"
```

---

### Task 4: GPU Backend (Basic Kernels)

**Files:**
- Create: `evaluation/src/fastmlfe2_eval/estimator/_gpu.py`

- [ ] **Step 1: Implement _gpu.py with basic global-memory kernels**

The basic kernel uses global memory (no shared-memory tiling). Tiled and fused kernels are added in Tasks 6-7.

```python
from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

if TYPE_CHECKING:
    from numpy.typing import NDArray
    from fastmlfe2_eval.estimator._types import EstimatorParams

import cupy as cp

from fastmlfe2_eval.estimator._types import compute_initial_means, compute_level_schedule

_resize_nearest_kernel = cp.RawKernel(
    r"""
extern "C" __global__
void resize_nearest(
    float *dst,
    const float *src,
    int w_src, int h_src,
    int w_dst, int h_dst,
    int depth
){
    int x_dst = blockDim.x * blockIdx.x + threadIdx.x;
    int y_dst = blockDim.y * blockIdx.y + threadIdx.y;
    if (x_dst >= w_dst || y_dst >= h_dst) return;

    int x_src = min(x_dst * w_src / w_dst, w_src - 1);
    int y_src = min(y_dst * h_src / h_dst, h_src - 1);

          float *ptr_dst = dst + (x_dst + y_dst * w_dst) * depth;
    const float *ptr_src = src + (x_src + y_src * w_src) * depth;

    for (int c = 0; c < depth; c++){
        ptr_dst[c] = ptr_src[c];
    }
}
""",
    "resize_nearest",
)

_ml_iterate_kernel = cp.RawKernel(
    r"""
extern "C" __global__
void ml_iterate(
    float *F,
    float *B,
    const float *F_prev,
    const float *B_prev,
    const float *image,
    const float *alpha,
    int w,
    int h,
    float regularization,
    float gradient_weight
){
    int x = blockDim.x * blockIdx.x + threadIdx.x;
    int y = blockDim.y * blockIdx.y + threadIdx.y;
    if (x >= w || y >= h) return;

    int i = y * w + x;
    float a0 = alpha[i];
    float a1 = 1.0f - a0;

    int nb[4] = {
        max(0, x - 1) + y * w,
        min(w - 1, x + 1) + y * w,
        x + max(0, y - 1) * w,
        x + min(h - 1, y + 1) * w,
    };

    float W = 0.0f;
    float sum_wF[3] = {0.0f, 0.0f, 0.0f};
    float sum_wB[3] = {0.0f, 0.0f, 0.0f};

    for (int d = 0; d < 4; d++){
        int j = nb[d];
        float wj = regularization + gradient_weight * fabsf(a0 - alpha[j]);
        W += wj;
        for (int c = 0; c < 3; c++){
            sum_wF[c] += wj * F_prev[j * 3 + c];
            sum_wB[c] += wj * B_prev[j * 3 + c];
        }
    }

    float inv_W = 1.0f / W;

    /* Binary pixel skip (H10) */
    if (a0 < 0.01f || a0 > 0.99f){
        float inv_Wp1 = 1.0f / (W + 1.0f);
        for (int c = 0; c < 3; c++){
            float mu_F = sum_wF[c] * inv_W;
            float mu_B = sum_wB[c] * inv_W;
            float r = image[i * 3 + c] - a0 * mu_F - a1 * mu_B;
            if (a0 < 0.01f){
                F[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_F));
                B[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_B + r * inv_Wp1));
            } else {
                F[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_F + r * inv_Wp1));
                B[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_B));
            }
        }
        return;
    }

    /* General case: mean-residual correction (H5) */
    float D = W + a0 * a0 + a1 * a1;
    float inv_D = 1.0f / D;
    float a0_inv_D = a0 * inv_D;
    float a1_inv_D = a1 * inv_D;

    for (int c = 0; c < 3; c++){
        float mu_F = sum_wF[c] * inv_W;
        float mu_B = sum_wB[c] * inv_W;
        float r = image[i * 3 + c] - a0 * mu_F - a1 * mu_B;
        F[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_F + a0_inv_D * r));
        B[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_B + a1_inv_D * r));
    }
}
""",
    "ml_iterate",
)

_BLOCK = (32, 32)


def _div_round_up(a: int, b: int) -> int:
    return (a + b - 1) // b


def _resize(dst, src, w_src, h_src, w_dst, h_dst, depth):
    grid = (_div_round_up(w_dst, _BLOCK[0]), _div_round_up(h_dst, _BLOCK[1]))
    _resize_nearest_kernel(grid, _BLOCK, (dst, src, w_src, h_src, w_dst, h_dst, depth))


def estimate_fb_ml(
    input_image: NDArray[np.float32],
    input_alpha: NDArray[np.float32],
    params: EstimatorParams,
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    h0, w0, depth = input_image.shape
    assert depth == 3

    schedule = compute_level_schedule(w0, h0, params)
    fg_mean, bg_mean = compute_initial_means(input_image, input_alpha)

    n = h0 * w0

    # Upload to device
    d_image = cp.asarray(input_image.astype(np.float32).reshape(-1))
    d_alpha = cp.asarray(input_alpha.astype(np.float32).reshape(-1))

    # Pre-allocate at max size
    d_F = cp.zeros(n * 3, dtype=cp.float32)
    d_B = cp.zeros(n * 3, dtype=cp.float32)
    d_F_prev = cp.zeros(n * 3, dtype=cp.float32)
    d_B_prev = cp.zeros(n * 3, dtype=cp.float32)
    d_image_level = cp.zeros(n * 3, dtype=cp.float32)
    d_alpha_level = cp.zeros(n, dtype=cp.float32)

    # Initialize 1×1 with mean colors
    d_F_prev[:3] = cp.asarray(fg_mean)
    d_B_prev[:3] = cp.asarray(bg_mean)

    w_prev, h_prev = 1, 1
    eps = np.float32(params.regularization)
    omega = np.float32(params.gradient_weight)

    for level in schedule:
        w, h, n_iter = level.w, level.h, level.n_iter

        # Resize input image and alpha to current level
        _resize(d_image_level, d_image, w0, h0, w, h, 3)
        _resize(d_alpha_level, d_alpha, w0, h0, w, h, 1)

        # Upsample F/B from previous level
        _resize(d_F, d_F_prev, w_prev, h_prev, w, h, 3)
        _resize(d_B, d_B_prev, w_prev, h_prev, w, h, 3)

        # d_F, d_B now have the upsampled initial guess
        # Copy to d_F_prev, d_B_prev for first iteration read
        cp.copyto(d_F_prev[: w * h * 3], d_F[: w * h * 3])
        cp.copyto(d_B_prev[: w * h * 3], d_B[: w * h * 3])

        grid = (_div_round_up(w, _BLOCK[0]), _div_round_up(h, _BLOCK[1]))

        for _i_iter in range(n_iter):
            _ml_iterate_kernel(
                grid,
                _BLOCK,
                (d_F, d_B, d_F_prev, d_B_prev, d_image_level, d_alpha_level, w, h, eps, omega),
            )
            # Swap: result in d_F → becomes d_F_prev for next iteration
            d_F_prev, d_F = d_F, d_F_prev
            d_B_prev, d_B = d_B, d_B_prev

        # After loop: d_F_prev has the latest result
        w_prev, h_prev = w, h

    # d_F_prev has final result
    F_out = cp.asnumpy(d_F_prev[: h0 * w0 * 3].reshape(h0, w0, 3))
    B_out = cp.asnumpy(d_B_prev[: h0 * w0 * 3].reshape(h0, w0, 3))
    return F_out, B_out
```

- [ ] **Step 2: Run all existing tests (should still pass for CPU)**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/ -v -k "not gpu"`
Expected: all PASS

- [ ] **Step 3: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add src/fastmlfe2_eval/estimator/_gpu.py
git commit -m "feat(estimator): add GPU backend with mean-residual Jacobi kernel"
```

---

### Task 5: GPU Property Tests + CPU/GPU Agreement

**Files:**
- Create: `evaluation/tests/test_estimator_gpu.py`

- [ ] **Step 1: Write GPU test file**

```python
import numpy as np
import pytest

try:
    import cupy  # noqa: F401

    HAS_CUPY = True
except ImportError:
    HAS_CUPY = False

from fastmlfe2_eval.estimator import estimate_foreground

pytestmark = pytest.mark.skipif(not HAS_CUPY, reason="CuPy not available")


def _make_composited(h=32, w=32, seed=42):
    rng = np.random.default_rng(seed)
    F_true = rng.random((h, w, 3)).astype(np.float32)
    B_true = rng.random((h, w, 3)).astype(np.float32)
    alpha = rng.random((h, w)).astype(np.float32)
    image = (alpha[:, :, np.newaxis] * F_true + (1 - alpha[:, :, np.newaxis]) * B_true).astype(
        np.float32
    )
    return image, alpha, F_true, B_true


class TestGPUProperties:
    def test_output_in_01(self):
        image, alpha, _, _ = _make_composited()
        F, B = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        assert np.all(F >= 0.0) and np.all(F <= 1.0)
        assert np.all(B >= 0.0) and np.all(B <= 1.0)

    def test_no_nan_inf(self):
        image, alpha, _, _ = _make_composited()
        F, B = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        assert np.all(np.isfinite(F)) and np.all(np.isfinite(B))

    def test_binary_alpha_zero(self):
        image = np.random.default_rng(0).random((16, 16, 3)).astype(np.float32)
        alpha = np.zeros((16, 16), dtype=np.float32)
        F, B = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        np.testing.assert_allclose(B, image, atol=0.05)

    def test_binary_alpha_one(self):
        image = np.random.default_rng(0).random((16, 16, 3)).astype(np.float32)
        alpha = np.ones((16, 16), dtype=np.float32)
        F = estimate_foreground(image, alpha, backend="gpu")
        np.testing.assert_allclose(F, image, atol=0.05)

    def test_convergence_monotone(self):
        """jacobiIterate_error_le: error decreases with more Jacobi iterations."""
        image, alpha, F_true, _ = _make_composited()
        err_prev = np.inf
        for n_iter in [1, 2, 5, 10]:
            F = estimate_foreground(
                image, alpha, backend="gpu", n_small_iterations=n_iter, n_big_iterations=n_iter
            )
            err = np.mean(np.abs(F - F_true))
            assert err <= err_prev + 1e-6, f"Error increased at n_iter={n_iter}"
            err_prev = err

    def test_fixed_point_stability(self):
        image, alpha, _, _ = _make_composited()
        F1 = estimate_foreground(image, alpha, backend="gpu")
        F2 = estimate_foreground(image, alpha, backend="gpu")
        np.testing.assert_allclose(F1, F2, atol=1e-5)

    def test_compositing_residual_bounded(self):
        image, alpha, _, _ = _make_composited()
        F, B = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        composite = alpha[:, :, np.newaxis] * F + (1 - alpha[:, :, np.newaxis]) * B
        residual = np.abs(composite - image)
        mask = (alpha > 0.1) & (alpha < 0.9)
        assert residual[mask].mean() < 0.1

    def test_1x1_image(self):
        image = np.array([[[0.5, 0.3, 0.7]]], dtype=np.float32)
        alpha = np.array([[0.6]], dtype=np.float32)
        F, B = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        assert F.shape == (1, 1, 3)
        assert np.all(np.isfinite(F)) and np.all(np.isfinite(B))

    def test_checkerboard_alpha(self):
        h, w = 16, 16
        image = np.random.default_rng(1).random((h, w, 3)).astype(np.float32)
        alpha = np.zeros((h, w), dtype=np.float32)
        alpha[::2, ::2] = 1.0
        alpha[1::2, 1::2] = 1.0
        F = estimate_foreground(image, alpha, backend="gpu")
        assert np.all(np.isfinite(F))
        assert np.all(F >= 0.0) and np.all(F <= 1.0)

    def test_non_multiple_of_32(self):
        """Tiled kernel must handle images not aligned to 32×32 tile boundaries."""
        image = np.random.default_rng(55).random((37, 41, 3)).astype(np.float32)
        alpha = np.random.default_rng(55).random((37, 41)).astype(np.float32)
        F = estimate_foreground(image, alpha, backend="gpu")
        assert np.all(np.isfinite(F))
        assert np.all(F >= 0.0) and np.all(F <= 1.0)


class TestMetricRegression:
    """SAD/MSE/GRAD regression on known ground-truth composited images."""

    def test_sad_mse_grad_reasonable(self):
        from fastmlfe2_eval.metrics import gradient_error, mse_error, sad_error

        image, alpha, F_true, B_true = _make_composited(h=64, w=64)
        F_est, B_est = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        mask = (alpha > 0.0) & (alpha < 1.0)
        weights = np.ones_like(alpha)

        sad = sad_error(F_est, F_true, weights, mask)
        mse = mse_error(F_est, F_true, weights, mask)
        grad = gradient_error(F_est, F_true, weights, mask)

        # Sanity bounds — not tight, just ensures the estimator is working
        assert sad < 500.0, f"SAD too large: {sad}"
        assert mse < 0.1, f"MSE too large: {mse}"
        assert grad < 500.0, f"GRAD too large: {grad}"


class TestCPUGPUAgreement:
    """Both backends implement the same mean-residual math.

    CPU uses red-black GS, GPU uses Jacobi — results differ slightly
    but should converge to similar solutions.
    """

    def test_agreement_random(self):
        image, alpha, _, _ = _make_composited(h=32, w=32)
        F_cpu = estimate_foreground(image, alpha, backend="cpu")
        F_gpu = estimate_foreground(image, alpha, backend="gpu")
        np.testing.assert_allclose(F_cpu, F_gpu, atol=1e-2)

    def test_agreement_binary_alpha(self):
        image = np.random.default_rng(7).random((16, 16, 3)).astype(np.float32)
        # Binary alpha: both backends should agree closely
        alpha = np.zeros((16, 16), dtype=np.float32)
        alpha[:8] = 1.0
        F_cpu = estimate_foreground(image, alpha, backend="cpu")
        F_gpu = estimate_foreground(image, alpha, backend="gpu")
        np.testing.assert_allclose(F_cpu, F_gpu, atol=1e-3)

    def test_agreement_gradient_alpha(self):
        image = np.random.default_rng(13).random((32, 32, 3)).astype(np.float32)
        alpha = np.linspace(0, 1, 32, dtype=np.float32)[np.newaxis, :].repeat(32, axis=0)
        F_cpu, B_cpu = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        F_gpu, B_gpu = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        np.testing.assert_allclose(F_cpu, F_gpu, atol=1e-2)
        np.testing.assert_allclose(B_cpu, B_gpu, atol=1e-2)
```

- [ ] **Step 2: Run GPU tests**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_estimator_gpu.py -v`
Expected: all PASS (or all SKIPPED if no GPU)

- [ ] **Step 3: Run full test suite**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/ -v`
Expected: all PASS (GPU tests may be SKIPPED)

- [ ] **Step 4: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add tests/test_estimator_gpu.py
git commit -m "test(estimator): add GPU property tests and CPU/GPU agreement tests"
```

---

### Task 6: GPU Optimization — Shared-Memory Tiled Kernel

**Files:**
- Modify: `evaluation/src/fastmlfe2_eval/estimator/_gpu.py`

Replace `_ml_iterate_kernel` with a shared-memory tiled version. The existing test suite validates correctness — output must match to within float32 precision.

- [ ] **Step 1: Add the tiled kernel to _gpu.py**

Add below the existing `_ml_iterate_kernel` definition (which is kept as fallback):

```python
_ml_iterate_tiled_kernel = cp.RawKernel(
    r"""
extern "C" __global__
void ml_iterate_tiled(
    float *F,
    float *B,
    const float *F_prev,
    const float *B_prev,
    const float *image,
    const float *alpha,
    int w,
    int h,
    float regularization,
    float gradient_weight
){
    const int TILE = 32;
    const int HT = 34;  /* TILE + 2 halo */

    __shared__ float s_Fp[HT * HT * 3];
    __shared__ float s_Bp[HT * HT * 3];
    __shared__ float s_a[HT * HT];

    int tx = threadIdx.x;
    int ty = threadIdx.y;
    int gx = blockIdx.x * TILE + tx;
    int gy = blockIdx.y * TILE + ty;

    /* shared-memory coords: center at (tx+1, ty+1) */
    int sx = tx + 1;
    int sy = ty + 1;
    int si = sy * HT + sx;

    /* --- Load center tile (clamp out-of-bounds to nearest edge pixel) --- */
    {
        int cx = min(w - 1, max(0, gx));
        int cy = min(h - 1, max(0, gy));
        int gi = cy * w + cx;
        s_a[si] = alpha[gi];
        for (int c = 0; c < 3; c++){
            s_Fp[si * 3 + c] = F_prev[gi * 3 + c];
            s_Bp[si * 3 + c] = B_prev[gi * 3 + c];
        }
    }

    /* --- Load halo --- */
    /* Left column */
    if (tx == 0){
        int hx = max(0, (int)(blockIdx.x * TILE) - 1);
        int hy = min(h - 1, max(0, gy));
        int gi = hy * w + hx;
        int hi = sy * HT;
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }
    /* Right column */
    if (tx == TILE - 1){
        int hx = min(w - 1, (int)(blockIdx.x * TILE) + TILE);
        int hy = min(h - 1, max(0, gy));
        int gi = hy * w + hx;
        int hi = sy * HT + TILE + 1;
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }
    /* Top row */
    if (ty == 0){
        int hx = min(w - 1, max(0, gx));
        int hy = max(0, (int)(blockIdx.y * TILE) - 1);
        int gi = hy * w + hx;
        int hi = sx;  /* row 0 */
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }
    /* Bottom row */
    if (ty == TILE - 1){
        int hx = min(w - 1, max(0, gx));
        int hy = min(h - 1, (int)(blockIdx.y * TILE) + TILE);
        int gi = hy * w + hx;
        int hi = (TILE + 1) * HT + sx;
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }
    /* Corners */
    if (tx == 0 && ty == 0){
        int hx = max(0, (int)(blockIdx.x * TILE) - 1);
        int hy = max(0, (int)(blockIdx.y * TILE) - 1);
        int gi = hy * w + hx;
        s_a[0] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[c] = F_prev[gi*3+c]; s_Bp[c] = B_prev[gi*3+c]; }
    }
    if (tx == TILE - 1 && ty == 0){
        int hx = min(w - 1, (int)(blockIdx.x * TILE) + TILE);
        int hy = max(0, (int)(blockIdx.y * TILE) - 1);
        int gi = hy * w + hx;
        int hi = TILE + 1;
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }
    if (tx == 0 && ty == TILE - 1){
        int hx = max(0, (int)(blockIdx.x * TILE) - 1);
        int hy = min(h - 1, (int)(blockIdx.y * TILE) + TILE);
        int gi = hy * w + hx;
        int hi = (TILE + 1) * HT;
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }
    if (tx == TILE - 1 && ty == TILE - 1){
        int hx = min(w - 1, (int)(blockIdx.x * TILE) + TILE);
        int hy = min(h - 1, (int)(blockIdx.y * TILE) + TILE);
        int gi = hy * w + hx;
        int hi = (TILE + 1) * HT + TILE + 1;
        s_a[hi] = alpha[gi];
        for (int c = 0; c < 3; c++){ s_Fp[hi*3+c] = F_prev[gi*3+c]; s_Bp[hi*3+c] = B_prev[gi*3+c]; }
    }

    __syncthreads();

    if (gx >= w || gy >= h) return;

    int gi = gy * w + gx;
    float a0 = s_a[si];
    float a1 = 1.0f - a0;

    /* Neighbor accumulation from shared memory */
    int nb[4] = {si - 1, si + 1, si - HT, si + HT};

    float W = 0.0f;
    float sum_wF[3] = {0.0f, 0.0f, 0.0f};
    float sum_wB[3] = {0.0f, 0.0f, 0.0f};

    for (int d = 0; d < 4; d++){
        int sj = nb[d];
        float wj = regularization + gradient_weight * fabsf(a0 - s_a[sj]);
        W += wj;
        for (int c = 0; c < 3; c++){
            sum_wF[c] += wj * s_Fp[sj * 3 + c];
            sum_wB[c] += wj * s_Bp[sj * 3 + c];
        }
    }

    float inv_W = 1.0f / W;

    if (a0 < 0.01f || a0 > 0.99f){
        float inv_Wp1 = 1.0f / (W + 1.0f);
        for (int c = 0; c < 3; c++){
            float mu_F = sum_wF[c] * inv_W;
            float mu_B = sum_wB[c] * inv_W;
            float r = image[gi * 3 + c] - a0 * mu_F - a1 * mu_B;
            if (a0 < 0.01f){
                F[gi*3+c] = fmaxf(0.0f, fminf(1.0f, mu_F));
                B[gi*3+c] = fmaxf(0.0f, fminf(1.0f, mu_B + r * inv_Wp1));
            } else {
                F[gi*3+c] = fmaxf(0.0f, fminf(1.0f, mu_F + r * inv_Wp1));
                B[gi*3+c] = fmaxf(0.0f, fminf(1.0f, mu_B));
            }
        }
        return;
    }

    float D = W + a0 * a0 + a1 * a1;
    float inv_D = 1.0f / D;
    float a0_inv_D = a0 * inv_D;
    float a1_inv_D = a1 * inv_D;

    for (int c = 0; c < 3; c++){
        float mu_F = sum_wF[c] * inv_W;
        float mu_B = sum_wB[c] * inv_W;
        float r = image[gi * 3 + c] - a0 * mu_F - a1 * mu_B;
        F[gi*3+c] = fmaxf(0.0f, fminf(1.0f, mu_F + a0_inv_D * r));
        B[gi*3+c] = fmaxf(0.0f, fminf(1.0f, mu_B + a1_inv_D * r));
    }
}
""",
    "ml_iterate_tiled",
)
```

- [ ] **Step 2: Switch the multi-level loop to use the tiled kernel**

In `estimate_fb_ml`, replace the `_ml_iterate_kernel` call with:
- Use `_ml_iterate_tiled_kernel` when `w >= 32 and h >= 32`
- Fall back to `_ml_iterate_kernel` for smaller levels (fewer than 32×32 pixels, tile larger than image)

```python
        for _i_iter in range(n_iter):
            if w >= 32 and h >= 32:
                _ml_iterate_tiled_kernel(
                    grid, _BLOCK,
                    (d_F, d_B, d_F_prev, d_B_prev, d_image_level, d_alpha_level,
                     w, h, eps, omega),
                )
            else:
                _ml_iterate_kernel(
                    grid, _BLOCK,
                    (d_F, d_B, d_F_prev, d_B_prev, d_image_level, d_alpha_level,
                     w, h, eps, omega),
                )
            d_F_prev, d_F = d_F, d_F_prev
            d_B_prev, d_B = d_B, d_B_prev
```

- [ ] **Step 3: Run GPU tests to verify correctness is preserved**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_estimator_gpu.py -v`
Expected: all PASS (same results as basic kernel)

- [ ] **Step 4: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add src/fastmlfe2_eval/estimator/_gpu.py
git commit -m "perf(estimator): add shared-memory tiled GPU kernel for large levels"
```

---

### Task 7: GPU Optimization — Fused Resize+Iterate Kernel

**Files:**
- Modify: `evaluation/src/fastmlfe2_eval/estimator/_gpu.py`

- [ ] **Step 1: Add fused kernel**

```python
_ml_fused_resize_iterate_kernel = cp.RawKernel(
    r"""
extern "C" __global__
void ml_fused_resize_iterate(
    float *F,
    float *B,
    const float *F_prev_level,
    const float *B_prev_level,
    const float *image,
    const float *alpha,
    int w, int h,
    int w_prev, int h_prev,
    float regularization,
    float gradient_weight
){
    int x = blockDim.x * blockIdx.x + threadIdx.x;
    int y = blockDim.y * blockIdx.y + threadIdx.y;
    if (x >= w || y >= h) return;

    int i = y * w + x;
    float a0 = alpha[i];
    float a1 = 1.0f - a0;

    /* Nearest-neighbor lookup into previous level */
    #define NN(gx, gy) \
        (min(h_prev - 1, max(0, (gy) * h_prev / h)) * w_prev + \
         min(w_prev - 1, max(0, (gx) * w_prev / w)))

    int nb_x[4] = {max(0, x-1), min(w-1, x+1), x, x};
    int nb_y[4] = {y, y, max(0, y-1), min(h-1, y+1)};

    float W = 0.0f;
    float sum_wF[3] = {0.0f, 0.0f, 0.0f};
    float sum_wB[3] = {0.0f, 0.0f, 0.0f};

    for (int d = 0; d < 4; d++){
        int j_prev = NN(nb_x[d], nb_y[d]);
        float a_nb = alpha[nb_y[d] * w + nb_x[d]];
        float wj = regularization + gradient_weight * fabsf(a0 - a_nb);
        W += wj;
        for (int c = 0; c < 3; c++){
            sum_wF[c] += wj * F_prev_level[j_prev * 3 + c];
            sum_wB[c] += wj * B_prev_level[j_prev * 3 + c];
        }
    }

    float inv_W = 1.0f / W;

    if (a0 < 0.01f || a0 > 0.99f){
        float inv_Wp1 = 1.0f / (W + 1.0f);
        for (int c = 0; c < 3; c++){
            float mu_F = sum_wF[c] * inv_W;
            float mu_B = sum_wB[c] * inv_W;
            float r = image[i * 3 + c] - a0 * mu_F - a1 * mu_B;
            if (a0 < 0.01f){
                F[i*3+c] = fmaxf(0.0f, fminf(1.0f, mu_F));
                B[i*3+c] = fmaxf(0.0f, fminf(1.0f, mu_B + r * inv_Wp1));
            } else {
                F[i*3+c] = fmaxf(0.0f, fminf(1.0f, mu_F + r * inv_Wp1));
                B[i*3+c] = fmaxf(0.0f, fminf(1.0f, mu_B));
            }
        }
        return;
    }

    float D = W + a0 * a0 + a1 * a1;
    float inv_D = 1.0f / D;
    float a0_inv_D = a0 * inv_D;
    float a1_inv_D = a1 * inv_D;

    for (int c = 0; c < 3; c++){
        float mu_F = sum_wF[c] * inv_W;
        float mu_B = sum_wB[c] * inv_W;
        float r = image[i * 3 + c] - a0 * mu_F - a1 * mu_B;
        F[i*3+c] = fmaxf(0.0f, fminf(1.0f, mu_F + a0_inv_D * r));
        B[i*3+c] = fmaxf(0.0f, fminf(1.0f, mu_B + a1_inv_D * r));
    }

    #undef NN
}
""",
    "ml_fused_resize_iterate",
)
```

- [ ] **Step 2: Update the multi-level loop to use the fused kernel for the first iteration**

Replace the iteration section in `estimate_fb_ml`:

```python
        # Resize input image and alpha to current level
        _resize(d_image_level, d_image, w0, h0, w, h, 3)
        _resize(d_alpha_level, d_alpha, w0, h0, w, h, 1)

        grid = (_div_round_up(w, _BLOCK[0]), _div_round_up(h, _BLOCK[1]))

        # First iteration: fused resize + iterate (reads from previous level's buffer)
        _ml_fused_resize_iterate_kernel(
            grid, _BLOCK,
            (d_F, d_B, d_F_prev, d_B_prev, d_image_level, d_alpha_level,
             w, h, w_prev, h_prev, eps, omega),
        )
        d_F_prev, d_F = d_F, d_F_prev
        d_B_prev, d_B = d_B, d_B_prev

        # Remaining iterations: tiled or basic kernel (current level buffers)
        for _i_iter in range(n_iter - 1):
            if w >= 32 and h >= 32:
                _ml_iterate_tiled_kernel(
                    grid, _BLOCK,
                    (d_F, d_B, d_F_prev, d_B_prev, d_image_level, d_alpha_level,
                     w, h, eps, omega),
                )
            else:
                _ml_iterate_kernel(
                    grid, _BLOCK,
                    (d_F, d_B, d_F_prev, d_B_prev, d_image_level, d_alpha_level,
                     w, h, eps, omega),
                )
            d_F_prev, d_F = d_F, d_F_prev
            d_B_prev, d_B = d_B, d_B_prev
```

This eliminates the separate resize + copy step for F/B at each level.

- [ ] **Step 3: Remove the now-unnecessary resize + copy for F/B**

Delete these lines from the loop body:

```python
        # DELETE THESE:
        _resize(d_F, d_F_prev, w_prev, h_prev, w, h, 3)
        _resize(d_B, d_B_prev, w_prev, h_prev, w, h, 3)
        cp.copyto(d_F_prev[: w * h * 3], d_F[: w * h * 3])
        cp.copyto(d_B_prev[: w * h * 3], d_B[: w * h * 3])
```

- [ ] **Step 4: Run GPU tests**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/test_estimator_gpu.py -v`
Expected: all PASS

- [ ] **Step 5: Run full test suite**

Run: `cd /home/nusu/Fast-ML-FE2/evaluation && uv run pytest tests/ -v`
Expected: all PASS

- [ ] **Step 6: Commit**

```bash
cd /home/nusu/Fast-ML-FE2/evaluation
git add src/fastmlfe2_eval/estimator/_gpu.py
git commit -m "perf(estimator): add fused resize+iterate GPU kernel, eliminate per-level copy"
```
