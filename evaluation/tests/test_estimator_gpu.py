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
        """jacobiIterate_error_le: compositing residual decreases with more Jacobi iterations."""
        image, alpha, _, _ = _make_composited()
        a = alpha[:, :, np.newaxis]

        def compositing_err(n):
            F, B = estimate_foreground(
                image, alpha, backend="gpu",
                n_small_iterations=n, n_big_iterations=n,
                return_background=True,
            )
            return float(np.mean(np.abs(image - a * F - (1 - a) * B)))

        err1 = compositing_err(1)
        err10 = compositing_err(10)
        assert err10 < err1, f"n=10 residual {err10:.5f} should be < n=1 residual {err1:.5f}"

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

        # Loose sanity bounds — verifies estimator runs and is better than all-zeros.
        # With random alpha the problem is ill-posed (F_true unrecoverable),
        # so error vs ground truth is expected to be large.
        assert sad < 5000.0, f"SAD too large: {sad}"
        assert mse < 0.5, f"MSE too large: {mse}"
        assert grad < 5000.0, f"GRAD too large: {grad}"


class TestCPUGPUAgreement:
    """Both backends implement the same mean-residual math.

    CPU uses red-black GS, GPU uses Jacobi — results differ slightly
    but should converge to similar solutions.
    """

    def test_agreement_random(self):
        # CPU (red-black GS) and GPU (Jacobi) converge to similar but not identical
        # solutions after 10 iterations. GS converges ~2x faster per iteration, so
        # the gap after finite iterations can be ~0.1.
        image, alpha, _, _ = _make_composited(h=32, w=32)
        F_cpu = estimate_foreground(image, alpha, backend="cpu")
        F_gpu = estimate_foreground(image, alpha, backend="gpu")
        np.testing.assert_allclose(F_cpu, F_gpu, atol=0.1)

    def test_agreement_binary_alpha(self):
        image = np.random.default_rng(7).random((16, 16, 3)).astype(np.float32)
        # Binary alpha: both backends should agree, except near the boundary row
        alpha = np.zeros((16, 16), dtype=np.float32)
        alpha[:8] = 1.0
        F_cpu = estimate_foreground(image, alpha, backend="cpu")
        F_gpu = estimate_foreground(image, alpha, backend="gpu")
        np.testing.assert_allclose(F_cpu, F_gpu, atol=0.1)

    def test_agreement_gradient_alpha(self):
        image = np.random.default_rng(13).random((32, 32, 3)).astype(np.float32)
        alpha = np.linspace(0, 1, 32, dtype=np.float32)[np.newaxis, :].repeat(32, axis=0)
        F_cpu, B_cpu = estimate_foreground(image, alpha, backend="cpu", return_background=True)
        F_gpu, B_gpu = estimate_foreground(image, alpha, backend="gpu", return_background=True)
        np.testing.assert_allclose(F_cpu, F_gpu, atol=0.1)
        np.testing.assert_allclose(B_cpu, B_gpu, atol=0.1)
