import numpy as np

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
        B_before = B.copy()
        _update_rb_half(F, B, image, alpha, h, w, 5e-3, 0.1, 0)  # red only

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

        _update_rb_half(F, B, image, alpha, h, w, 5e-3, 0.1, 0)
        _update_rb_half(F, B, image, alpha, h, w, 5e-3, 0.1, 1)

        assert np.all(F >= 0.0) and np.all(F <= 1.0)
        assert np.all(B >= 0.0) and np.all(B <= 1.0)
