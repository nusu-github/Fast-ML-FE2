from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np
from numba import njit, prange

if TYPE_CHECKING:
    from numpy.typing import NDArray

    from fastmlfe2_eval.estimator._types import EstimatorParams

from fastmlfe2_eval.estimator._types import compute_initial_means, compute_level_schedule


@njit("void(f4[:,:,:], f4[:,:,:])", cache=True, nogil=True, parallel=True)
def _resize_nearest_multichannel(dst, src):
    h_src, w_src, depth = src.shape
    h_dst, w_dst, _depth = dst.shape
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
