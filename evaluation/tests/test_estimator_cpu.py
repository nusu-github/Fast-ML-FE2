import numpy as np
import pytest

from fastmlfe2_eval.estimator import estimate_foreground
from fastmlfe2_eval.estimator import _cpu as cpu_backend
from fastmlfe2_eval.estimator._cpu import (
    _build_level_coefficients,
    _resize_nearest,
    _resize_nearest_multichannel,
    _update_rb_half_cached,
)


def _build_cached_kernel_inputs(alpha, eps, omega):
    """Allocate and populate the cached-kernel coefficient buffers."""
    h, w = alpha.shape
    neighbor_weights = np.empty((h, w, 4), dtype=np.float32)
    inv_W = np.empty((h, w), dtype=np.float32)
    inv_Wp1 = np.empty((h, w), dtype=np.float32)
    fg_gain = np.empty((h, w), dtype=np.float32)
    bg_gain = np.empty((h, w), dtype=np.float32)
    _build_level_coefficients(
        alpha,
        np.float32(eps),
        np.float32(omega),
        neighbor_weights,
        inv_W,
        inv_Wp1,
        fg_gain,
        bg_gain,
    )
    return neighbor_weights, inv_W, inv_Wp1, fg_gain, bg_gain


def test_cpu_backend_reexports_native_helpers():
    expected = {
        "_build_level_coefficients",
        "_resize_nearest",
        "_resize_nearest_multichannel",
        "_update_rb_half_cached",
        "_update_rb_half_cached_from_prev_level",
        "_update_rb_half_cached_from_prev_level_with_boundary_fallback",
        "estimate_fb_ml",
    }
    assert expected.issubset(set(cpu_backend.__all__))


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

        coeffs = _build_cached_kernel_inputs(alpha, 0.1, 0.0)
        _update_rb_half_cached(F, B, image, alpha, *coeffs, h, w, 0)  # red

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

        coeffs = _build_cached_kernel_inputs(alpha, 0.1, 0.0)
        _update_rb_half_cached(F, B, image, alpha, *coeffs, h, w, 0)

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

        coeffs = _build_cached_kernel_inputs(alpha, 0.1, 0.0)
        _update_rb_half_cached(F, B, image, alpha, *coeffs, h, w, 0)

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
        B_before = B.copy()
        coeffs = _build_cached_kernel_inputs(alpha, 5e-3, 0.1)
        _update_rb_half_cached(F, B, image, alpha, *coeffs, h, w, 0)  # red only

        # Black pixels should be unchanged in both F and B
        for y in range(h):
            for x in range(w):
                if (x + y) % 2 == 1:  # black
                    np.testing.assert_array_equal(F[y, x], F_before[y, x])
                    np.testing.assert_array_equal(B[y, x], B_before[y, x])

    def test_output_bounded_01(self):
        """Output should always be in [0, 1] regardless of input."""
        rng = np.random.default_rng(99)
        h, w = 16, 16
        F = rng.random((h, w, 3)).astype(np.float32)
        B = rng.random((h, w, 3)).astype(np.float32)
        image = rng.random((h, w, 3)).astype(np.float32)
        alpha = rng.random((h, w)).astype(np.float32)

        coeffs = _build_cached_kernel_inputs(alpha, 5e-3, 0.1)
        _update_rb_half_cached(F, B, image, alpha, *coeffs, h, w, 0)
        _update_rb_half_cached(F, B, image, alpha, *coeffs, h, w, 1)

        assert np.all(F >= 0.0) and np.all(F <= 1.0)
        assert np.all(B >= 0.0) and np.all(B <= 1.0)


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
        """Empirical: compositing residual should decrease with more iterations.

        Red-black GS minimizes the compositing energy, so |I - αF - (1-α)B|
        should be lower after 10 iterations than after 1. We measure this energy
        (not error vs ground truth, which the algorithm does not optimize).
        """
        image, alpha, _, _ = _make_composited()
        a = alpha[:, :, np.newaxis]

        def compositing_err(n):
            F, B = estimate_foreground(
                image,
                alpha,
                backend="cpu",
                n_small_iterations=n,
                n_big_iterations=n,
                return_background=True,
            )
            return float(np.mean(np.abs(image - a * F - (1 - a) * B)))

        err1 = compositing_err(1)
        err10 = compositing_err(10)
        msg = f"n=10 residual {err10:.5f} should be less than n=1 residual {err1:.5f}"
        assert err10 < err1, msg

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


def _make_quantized_pattern(
    h: int = 64,
    w: int = 64,
    seed: int = 123,
) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    yy, xx = np.mgrid[0:h, 0:w]
    x = xx.astype(np.float32) / max(w - 1, 1)
    y = yy.astype(np.float32) / max(h - 1, 1)

    checker = ((xx // 9 + yy // 11) & 1).astype(np.float32)
    image = np.stack(
        [
            0.10 + 0.72 * x + 0.08 * checker,
            0.18 + 0.62 * y + 0.10 * np.sin(6.0 * np.pi * x),
            0.22 + 0.48 * (1.0 - x) * (1.0 - y) + 0.08 * rng.random((h, w), dtype=np.float32),
        ],
        axis=2,
    )
    alpha = 0.5 + 0.34 * np.sin(4.0 * np.pi * (x + 0.15 * y)) * np.cos(3.0 * np.pi * (y - 0.2 * x))
    alpha += 0.08 * checker - 0.05 * rng.random((h, w), dtype=np.float32)

    image = np.clip(image, 0.0, 1.0)
    alpha = np.clip(alpha, 0.0, 1.0)

    return np.rint(image * 255.0).astype(np.uint8), np.rint(alpha * 255.0).astype(np.uint8)


class TestCPUu8Backend:
    def test_accepts_uint8_and_returns_uint8(self):
        image_u8, alpha_u8 = _make_quantized_pattern(32, 32)
        foreground, background = estimate_foreground(
            image_u8,
            alpha_u8,
            backend="cpu_u8",
            return_background=True,
        )

        assert foreground.dtype == np.uint8
        assert background.dtype == np.uint8
        assert foreground.shape == image_u8.shape
        assert background.shape == image_u8.shape
        assert np.all(foreground <= 255)
        assert np.all(background <= 255)

    def test_rejects_non_uint8_inputs(self):
        image_u8, alpha_u8 = _make_quantized_pattern(16, 16)
        with pytest.raises(ValueError, match="cpu_u8 backend requires uint8 image"):
            estimate_foreground(image_u8.astype(np.float32) / 255.0, alpha_u8, backend="cpu_u8")
        with pytest.raises(ValueError, match="cpu_u8 backend requires uint8 alpha"):
            estimate_foreground(image_u8, alpha_u8.astype(np.float32) / 255.0, backend="cpu_u8")

    def test_matches_float32_cpu_on_quantized_pattern(self):
        image_u8, alpha_u8 = _make_quantized_pattern(64, 64, seed=7)
        image_f32 = image_u8.astype(np.float32) / 255.0
        alpha_f32 = alpha_u8.astype(np.float32) / 255.0

        cpu_u8_f, cpu_u8_b = estimate_foreground(
            image_u8,
            alpha_u8,
            backend="cpu_u8",
            return_background=True,
        )
        cpu_f32_f, cpu_f32_b = estimate_foreground(
            image_f32,
            alpha_f32,
            backend="cpu",
            return_background=True,
        )

        cpu_u8_f32 = cpu_u8_f.astype(np.float32) / 255.0
        cpu_u8_b32 = cpu_u8_b.astype(np.float32) / 255.0
        np.testing.assert_allclose(cpu_u8_f32, cpu_f32_f, atol=0.05, rtol=0.0)
        np.testing.assert_allclose(cpu_u8_b32, cpu_f32_b, atol=0.05, rtol=0.0)

    def test_large_shape_smoke(self):
        image_u8, alpha_u8 = _make_quantized_pattern(1024, 1024, seed=11)
        foreground = estimate_foreground(image_u8, alpha_u8, backend="cpu_u8")
        assert foreground.dtype == np.uint8
        assert foreground.shape == image_u8.shape

    def test_repeated_calls_with_same_shape_are_stable(self):
        image_u8, alpha_u8 = _make_quantized_pattern(96, 80, seed=21)
        first_f, first_b = estimate_foreground(
            image_u8,
            alpha_u8,
            backend="cpu_u8",
            return_background=True,
        )
        second_f, second_b = estimate_foreground(
            image_u8,
            alpha_u8,
            backend="cpu_u8",
            return_background=True,
        )

        np.testing.assert_array_equal(first_f, second_f)
        np.testing.assert_array_equal(first_b, second_b)

    def test_repeated_calls_with_different_shapes_are_stable(self):
        small_image, small_alpha = _make_quantized_pattern(48, 40, seed=30)
        large_image, large_alpha = _make_quantized_pattern(72, 88, seed=31)

        small_f0, small_b0 = estimate_foreground(
            small_image,
            small_alpha,
            backend="cpu_u8",
            return_background=True,
        )
        estimate_foreground(
            large_image,
            large_alpha,
            backend="cpu_u8",
            return_background=True,
        )
        small_f1, small_b1 = estimate_foreground(
            small_image,
            small_alpha,
            backend="cpu_u8",
            return_background=True,
        )

        np.testing.assert_array_equal(small_f0, small_f1)
        np.testing.assert_array_equal(small_b0, small_b1)
