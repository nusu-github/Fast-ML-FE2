from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np
from numba import njit, prange

if TYPE_CHECKING:
    from numpy.typing import NDArray

    from fastmlfe2_eval.estimator._types import EstimatorParams

from fastmlfe2_eval.estimator._types import (
    compute_initial_means,
    compute_level_schedule,
)


def _resize_index_map(src_size: int, dst_size: int) -> np.ndarray:
    coords = np.arange(dst_size, dtype=np.int32)
    return np.minimum(src_size - 1, coords * src_size // dst_size).astype(np.int32)


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
def _update_rb_half_cached(
    F,
    B,
    image,
    alpha,
    neighbor_weights,
    inv_W,
    inv_Wp1,
    fg_gain,
    bg_gain,
    h,
    w,
    color,
):
    dx = [-1, 1, 0, 0]
    dy = [0, 0, -1, 1]

    for y in prange(h):
        x_start = (color + y) % 2
        for x in range(x_start, w, 2):
            a0 = alpha[y, x]
            a1 = 1.0 - a0

            if 0 < x < w - 1 and 0 < y < h - 1:
                sum_wF0 = 0.0
                sum_wF1 = 0.0
                sum_wF2 = 0.0
                sum_wB0 = 0.0
                sum_wB1 = 0.0
                sum_wB2 = 0.0

                for d in range(4):
                    wj = neighbor_weights[y, x, d]
                    x2 = x + dx[d]
                    y2 = y + dy[d]
                    sum_wF0 += wj * F[y2, x2, 0]
                    sum_wF1 += wj * F[y2, x2, 1]
                    sum_wF2 += wj * F[y2, x2, 2]
                    sum_wB0 += wj * B[y2, x2, 0]
                    sum_wB1 += wj * B[y2, x2, 1]
                    sum_wB2 += wj * B[y2, x2, 2]

                inv_W_local = inv_W[y, x]

                if a0 < 0.01 or a0 > 0.99:
                    inv_Wp1_local = inv_Wp1[y, x]
                    mu_F0 = sum_wF0 * inv_W_local
                    mu_B0 = sum_wB0 * inv_W_local
                    r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
                    mu_F1 = sum_wF1 * inv_W_local
                    mu_B1 = sum_wB1 * inv_W_local
                    r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
                    mu_F2 = sum_wF2 * inv_W_local
                    mu_B2 = sum_wB2 * inv_W_local
                    r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2
                    if a0 < 0.01:
                        F[y, x, 0] = max(0.0, min(1.0, mu_F0))
                        F[y, x, 1] = max(0.0, min(1.0, mu_F1))
                        F[y, x, 2] = max(0.0, min(1.0, mu_F2))
                        B[y, x, 0] = max(0.0, min(1.0, mu_B0 + r0 * inv_Wp1_local))
                        B[y, x, 1] = max(0.0, min(1.0, mu_B1 + r1 * inv_Wp1_local))
                        B[y, x, 2] = max(0.0, min(1.0, mu_B2 + r2 * inv_Wp1_local))
                    else:
                        F[y, x, 0] = max(0.0, min(1.0, mu_F0 + r0 * inv_Wp1_local))
                        F[y, x, 1] = max(0.0, min(1.0, mu_F1 + r1 * inv_Wp1_local))
                        F[y, x, 2] = max(0.0, min(1.0, mu_F2 + r2 * inv_Wp1_local))
                        B[y, x, 0] = max(0.0, min(1.0, mu_B0))
                        B[y, x, 1] = max(0.0, min(1.0, mu_B1))
                        B[y, x, 2] = max(0.0, min(1.0, mu_B2))
                    continue

            sum_wF0 = 0.0
            sum_wF1 = 0.0
            sum_wF2 = 0.0
            sum_wB0 = 0.0
            sum_wB1 = 0.0
            sum_wB2 = 0.0

            for d in range(4):
                x2 = max(0, min(w - 1, x + dx[d]))
                y2 = max(0, min(h - 1, y + dy[d]))
                wj = neighbor_weights[y, x, d]
                sum_wF0 += wj * F[y2, x2, 0]
                sum_wF1 += wj * F[y2, x2, 1]
                sum_wF2 += wj * F[y2, x2, 2]
                sum_wB0 += wj * B[y2, x2, 0]
                sum_wB1 += wj * B[y2, x2, 1]
                sum_wB2 += wj * B[y2, x2, 2]

            inv_W_local = inv_W[y, x]

            if a0 < 0.01 or a0 > 0.99:
                inv_Wp1_local = inv_Wp1[y, x]
                mu_F0 = sum_wF0 * inv_W_local
                mu_B0 = sum_wB0 * inv_W_local
                r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
                mu_F1 = sum_wF1 * inv_W_local
                mu_B1 = sum_wB1 * inv_W_local
                r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
                mu_F2 = sum_wF2 * inv_W_local
                mu_B2 = sum_wB2 * inv_W_local
                r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2
                if a0 < 0.01:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0 + r0 * inv_Wp1_local))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1 + r1 * inv_Wp1_local))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2 + r2 * inv_Wp1_local))
                else:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0 + r0 * inv_Wp1_local))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1 + r1 * inv_Wp1_local))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2 + r2 * inv_Wp1_local))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2))
                continue

            fg_g = fg_gain[y, x]
            bg_g = bg_gain[y, x]

            mu_F0 = sum_wF0 * inv_W_local
            mu_B0 = sum_wB0 * inv_W_local
            r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
            mu_F1 = sum_wF1 * inv_W_local
            mu_B1 = sum_wB1 * inv_W_local
            r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
            mu_F2 = sum_wF2 * inv_W_local
            mu_B2 = sum_wB2 * inv_W_local
            r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2

            F[y, x, 0] = max(0.0, min(1.0, mu_F0 + fg_g * r0))
            F[y, x, 1] = max(0.0, min(1.0, mu_F1 + fg_g * r1))
            F[y, x, 2] = max(0.0, min(1.0, mu_F2 + fg_g * r2))
            B[y, x, 0] = max(0.0, min(1.0, mu_B0 + bg_g * r0))
            B[y, x, 1] = max(0.0, min(1.0, mu_B1 + bg_g * r1))
            B[y, x, 2] = max(0.0, min(1.0, mu_B2 + bg_g * r2))


@njit(cache=True, nogil=True, parallel=True)
def _update_rb_half_cached_from_prev_level(
    F,
    B,
    image,
    alpha,
    neighbor_weights,
    inv_W,
    inv_Wp1,
    fg_gain,
    bg_gain,
    F_prev,
    B_prev,
    x_prev_map,
    y_prev_map,
    h,
    w,
):
    """First red half-sweep fused with coarse-to-fine nearest-neighbor reads."""
    for y in prange(h):
        x_start = y % 2
        y_current_prev = y_prev_map[y]
        y_up = max(0, y - 1)
        y_down = min(h - 1, y + 1)
        y_up_prev = y_prev_map[y_up]
        y_down_prev = y_prev_map[y_down]
        for x in range(x_start, w, 2):
            a0 = alpha[y, x]
            a1 = 1.0 - a0

            if 0 < x < w - 1 and 0 < y < h - 1:
                y_prev = y_current_prev
                x_prev = x_prev_map[x]
                x_left_prev = x_prev_map[x - 1]
                x_right_prev = x_prev_map[x + 1]
                sum_wF0 = 0.0
                sum_wF1 = 0.0
                sum_wF2 = 0.0
                sum_wB0 = 0.0
                sum_wB1 = 0.0
                sum_wB2 = 0.0

                wj = neighbor_weights[y, x, 0]
                sum_wF0 += wj * F_prev[y_prev, x_left_prev, 0]
                sum_wF1 += wj * F_prev[y_prev, x_left_prev, 1]
                sum_wF2 += wj * F_prev[y_prev, x_left_prev, 2]
                sum_wB0 += wj * B_prev[y_prev, x_left_prev, 0]
                sum_wB1 += wj * B_prev[y_prev, x_left_prev, 1]
                sum_wB2 += wj * B_prev[y_prev, x_left_prev, 2]

                wj = neighbor_weights[y, x, 1]
                sum_wF0 += wj * F_prev[y_prev, x_right_prev, 0]
                sum_wF1 += wj * F_prev[y_prev, x_right_prev, 1]
                sum_wF2 += wj * F_prev[y_prev, x_right_prev, 2]
                sum_wB0 += wj * B_prev[y_prev, x_right_prev, 0]
                sum_wB1 += wj * B_prev[y_prev, x_right_prev, 1]
                sum_wB2 += wj * B_prev[y_prev, x_right_prev, 2]

                wj = neighbor_weights[y, x, 2]
                sum_wF0 += wj * F_prev[y_up_prev, x_prev, 0]
                sum_wF1 += wj * F_prev[y_up_prev, x_prev, 1]
                sum_wF2 += wj * F_prev[y_up_prev, x_prev, 2]
                sum_wB0 += wj * B_prev[y_up_prev, x_prev, 0]
                sum_wB1 += wj * B_prev[y_up_prev, x_prev, 1]
                sum_wB2 += wj * B_prev[y_up_prev, x_prev, 2]

                wj = neighbor_weights[y, x, 3]
                sum_wF0 += wj * F_prev[y_down_prev, x_prev, 0]
                sum_wF1 += wj * F_prev[y_down_prev, x_prev, 1]
                sum_wF2 += wj * F_prev[y_down_prev, x_prev, 2]
                sum_wB0 += wj * B_prev[y_down_prev, x_prev, 0]
                sum_wB1 += wj * B_prev[y_down_prev, x_prev, 1]
                sum_wB2 += wj * B_prev[y_down_prev, x_prev, 2]

                inv_W_local = inv_W[y, x]
                inv_Wp1_local = inv_Wp1[y, x]
                mu_F0 = sum_wF0 * inv_W_local
                mu_B0 = sum_wB0 * inv_W_local
                r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
                mu_F1 = sum_wF1 * inv_W_local
                mu_B1 = sum_wB1 * inv_W_local
                r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
                mu_F2 = sum_wF2 * inv_W_local
                mu_B2 = sum_wB2 * inv_W_local
                r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2

                if a0 < 0.01:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0 + r0 * inv_Wp1_local))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1 + r1 * inv_Wp1_local))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2 + r2 * inv_Wp1_local))
                elif a0 > 0.99:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0 + r0 * inv_Wp1_local))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1 + r1 * inv_Wp1_local))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2 + r2 * inv_Wp1_local))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2))
                else:
                    fg_g = fg_gain[y, x]
                    bg_g = bg_gain[y, x]
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0 + fg_g * r0))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1 + fg_g * r1))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2 + fg_g * r2))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0 + bg_g * r0))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1 + bg_g * r1))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2 + bg_g * r2))
                continue

            x_left = max(0, x - 1)
            x_right = min(w - 1, x + 1)
            x_left_prev = x_prev_map[x_left]
            x_current_prev = x_prev_map[x]
            x_right_prev = x_prev_map[x_right]

            sum_wF0 = 0.0
            sum_wF1 = 0.0
            sum_wF2 = 0.0
            sum_wB0 = 0.0
            sum_wB1 = 0.0
            sum_wB2 = 0.0

            wj = neighbor_weights[y, x, 0]
            sum_wF0 += wj * F_prev[y_current_prev, x_left_prev, 0]
            sum_wF1 += wj * F_prev[y_current_prev, x_left_prev, 1]
            sum_wF2 += wj * F_prev[y_current_prev, x_left_prev, 2]
            sum_wB0 += wj * B_prev[y_current_prev, x_left_prev, 0]
            sum_wB1 += wj * B_prev[y_current_prev, x_left_prev, 1]
            sum_wB2 += wj * B_prev[y_current_prev, x_left_prev, 2]

            wj = neighbor_weights[y, x, 1]
            sum_wF0 += wj * F_prev[y_current_prev, x_right_prev, 0]
            sum_wF1 += wj * F_prev[y_current_prev, x_right_prev, 1]
            sum_wF2 += wj * F_prev[y_current_prev, x_right_prev, 2]
            sum_wB0 += wj * B_prev[y_current_prev, x_right_prev, 0]
            sum_wB1 += wj * B_prev[y_current_prev, x_right_prev, 1]
            sum_wB2 += wj * B_prev[y_current_prev, x_right_prev, 2]

            wj = neighbor_weights[y, x, 2]
            sum_wF0 += wj * F_prev[y_up_prev, x_current_prev, 0]
            sum_wF1 += wj * F_prev[y_up_prev, x_current_prev, 1]
            sum_wF2 += wj * F_prev[y_up_prev, x_current_prev, 2]
            sum_wB0 += wj * B_prev[y_up_prev, x_current_prev, 0]
            sum_wB1 += wj * B_prev[y_up_prev, x_current_prev, 1]
            sum_wB2 += wj * B_prev[y_up_prev, x_current_prev, 2]

            wj = neighbor_weights[y, x, 3]
            sum_wF0 += wj * F_prev[y_down_prev, x_current_prev, 0]
            sum_wF1 += wj * F_prev[y_down_prev, x_current_prev, 1]
            sum_wF2 += wj * F_prev[y_down_prev, x_current_prev, 2]
            sum_wB0 += wj * B_prev[y_down_prev, x_current_prev, 0]
            sum_wB1 += wj * B_prev[y_down_prev, x_current_prev, 1]
            sum_wB2 += wj * B_prev[y_down_prev, x_current_prev, 2]

            inv_W_local = inv_W[y, x]
            inv_Wp1_local = inv_Wp1[y, x]

            mu_F0 = sum_wF0 * inv_W_local
            mu_B0 = sum_wB0 * inv_W_local
            r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
            mu_F1 = sum_wF1 * inv_W_local
            mu_B1 = sum_wB1 * inv_W_local
            r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
            mu_F2 = sum_wF2 * inv_W_local
            mu_B2 = sum_wB2 * inv_W_local
            r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2

            if a0 < 0.01 or a0 > 0.99:
                if a0 < 0.01:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0 + r0 * inv_Wp1_local))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1 + r1 * inv_Wp1_local))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2 + r2 * inv_Wp1_local))
                else:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0 + r0 * inv_Wp1_local))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1 + r1 * inv_Wp1_local))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2 + r2 * inv_Wp1_local))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2))
                continue

            fg_g = fg_gain[y, x]
            bg_g = bg_gain[y, x]

            F[y, x, 0] = max(0.0, min(1.0, mu_F0 + fg_g * r0))
            F[y, x, 1] = max(0.0, min(1.0, mu_F1 + fg_g * r1))
            F[y, x, 2] = max(0.0, min(1.0, mu_F2 + fg_g * r2))
            B[y, x, 0] = max(0.0, min(1.0, mu_B0 + bg_g * r0))
            B[y, x, 1] = max(0.0, min(1.0, mu_B1 + bg_g * r1))
            B[y, x, 2] = max(0.0, min(1.0, mu_B2 + bg_g * r2))


@njit(cache=True, nogil=True, parallel=True)
def _update_rb_half_cached_from_prev_level_with_boundary_fallback(
    F,
    B,
    image,
    alpha,
    neighbor_weights,
    inv_W,
    inv_Wp1,
    fg_gain,
    bg_gain,
    F_prev,
    B_prev,
    x_prev_map,
    y_prev_map,
    h,
    w,
):
    """Second half-sweep for the first iteration.

    Red neighbors are read from the current fine-level buffers. If clamping makes a
    neighbor coincide with the active black pixel itself, fall back to the coarse
    previous level so we do not need a fully materialized fine-level F/B buffer.
    """
    for y in prange(h):
        x_start = (1 + y) % 2
        y_current_prev = y_prev_map[y]
        y_up = max(0, y - 1)
        y_down = min(h - 1, y + 1)
        for x in range(x_start, w, 2):
            a0 = alpha[y, x]
            a1 = 1.0 - a0

            if 0 < x < w - 1 and 0 < y < h - 1:
                sum_wF0 = 0.0
                sum_wF1 = 0.0
                sum_wF2 = 0.0
                sum_wB0 = 0.0
                sum_wB1 = 0.0
                sum_wB2 = 0.0

                wj = neighbor_weights[y, x, 0]
                sum_wF0 += wj * F[y, x - 1, 0]
                sum_wF1 += wj * F[y, x - 1, 1]
                sum_wF2 += wj * F[y, x - 1, 2]
                sum_wB0 += wj * B[y, x - 1, 0]
                sum_wB1 += wj * B[y, x - 1, 1]
                sum_wB2 += wj * B[y, x - 1, 2]

                wj = neighbor_weights[y, x, 1]
                sum_wF0 += wj * F[y, x + 1, 0]
                sum_wF1 += wj * F[y, x + 1, 1]
                sum_wF2 += wj * F[y, x + 1, 2]
                sum_wB0 += wj * B[y, x + 1, 0]
                sum_wB1 += wj * B[y, x + 1, 1]
                sum_wB2 += wj * B[y, x + 1, 2]

                wj = neighbor_weights[y, x, 2]
                sum_wF0 += wj * F[y - 1, x, 0]
                sum_wF1 += wj * F[y - 1, x, 1]
                sum_wF2 += wj * F[y - 1, x, 2]
                sum_wB0 += wj * B[y - 1, x, 0]
                sum_wB1 += wj * B[y - 1, x, 1]
                sum_wB2 += wj * B[y - 1, x, 2]

                wj = neighbor_weights[y, x, 3]
                sum_wF0 += wj * F[y + 1, x, 0]
                sum_wF1 += wj * F[y + 1, x, 1]
                sum_wF2 += wj * F[y + 1, x, 2]
                sum_wB0 += wj * B[y + 1, x, 0]
                sum_wB1 += wj * B[y + 1, x, 1]
                sum_wB2 += wj * B[y + 1, x, 2]

                inv_W_local = inv_W[y, x]

                if a0 < 0.01 or a0 > 0.99:
                    inv_Wp1_local = inv_Wp1[y, x]
                    mu_F0 = sum_wF0 * inv_W_local
                    mu_B0 = sum_wB0 * inv_W_local
                    r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
                    mu_F1 = sum_wF1 * inv_W_local
                    mu_B1 = sum_wB1 * inv_W_local
                    r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
                    mu_F2 = sum_wF2 * inv_W_local
                    mu_B2 = sum_wB2 * inv_W_local
                    r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2
                    if a0 < 0.01:
                        F[y, x, 0] = max(0.0, min(1.0, mu_F0))
                        F[y, x, 1] = max(0.0, min(1.0, mu_F1))
                        F[y, x, 2] = max(0.0, min(1.0, mu_F2))
                        B[y, x, 0] = max(0.0, min(1.0, mu_B0 + r0 * inv_Wp1_local))
                        B[y, x, 1] = max(0.0, min(1.0, mu_B1 + r1 * inv_Wp1_local))
                        B[y, x, 2] = max(0.0, min(1.0, mu_B2 + r2 * inv_Wp1_local))
                    else:
                        F[y, x, 0] = max(0.0, min(1.0, mu_F0 + r0 * inv_Wp1_local))
                        F[y, x, 1] = max(0.0, min(1.0, mu_F1 + r1 * inv_Wp1_local))
                        F[y, x, 2] = max(0.0, min(1.0, mu_F2 + r2 * inv_Wp1_local))
                        B[y, x, 0] = max(0.0, min(1.0, mu_B0))
                        B[y, x, 1] = max(0.0, min(1.0, mu_B1))
                        B[y, x, 2] = max(0.0, min(1.0, mu_B2))
                    continue

            x_left = max(0, x - 1)
            x_right = min(w - 1, x + 1)
            x_current_prev = x_prev_map[x]

            sum_wF0 = 0.0
            sum_wF1 = 0.0
            sum_wF2 = 0.0
            sum_wB0 = 0.0
            sum_wB1 = 0.0
            sum_wB2 = 0.0

            # Left neighbor.
            wj = neighbor_weights[y, x, 0]
            if x_left == x:
                sum_wF0 += wj * F_prev[y_current_prev, x_current_prev, 0]
                sum_wF1 += wj * F_prev[y_current_prev, x_current_prev, 1]
                sum_wF2 += wj * F_prev[y_current_prev, x_current_prev, 2]
                sum_wB0 += wj * B_prev[y_current_prev, x_current_prev, 0]
                sum_wB1 += wj * B_prev[y_current_prev, x_current_prev, 1]
                sum_wB2 += wj * B_prev[y_current_prev, x_current_prev, 2]
            else:
                sum_wF0 += wj * F[y, x_left, 0]
                sum_wF1 += wj * F[y, x_left, 1]
                sum_wF2 += wj * F[y, x_left, 2]
                sum_wB0 += wj * B[y, x_left, 0]
                sum_wB1 += wj * B[y, x_left, 1]
                sum_wB2 += wj * B[y, x_left, 2]

            # Right neighbor.
            wj = neighbor_weights[y, x, 1]
            if x_right == x:
                sum_wF0 += wj * F_prev[y_current_prev, x_current_prev, 0]
                sum_wF1 += wj * F_prev[y_current_prev, x_current_prev, 1]
                sum_wF2 += wj * F_prev[y_current_prev, x_current_prev, 2]
                sum_wB0 += wj * B_prev[y_current_prev, x_current_prev, 0]
                sum_wB1 += wj * B_prev[y_current_prev, x_current_prev, 1]
                sum_wB2 += wj * B_prev[y_current_prev, x_current_prev, 2]
            else:
                sum_wF0 += wj * F[y, x_right, 0]
                sum_wF1 += wj * F[y, x_right, 1]
                sum_wF2 += wj * F[y, x_right, 2]
                sum_wB0 += wj * B[y, x_right, 0]
                sum_wB1 += wj * B[y, x_right, 1]
                sum_wB2 += wj * B[y, x_right, 2]

            # Up neighbor.
            wj = neighbor_weights[y, x, 2]
            y2 = y_up
            if y2 == y:
                sum_wF0 += wj * F_prev[y_current_prev, x_current_prev, 0]
                sum_wF1 += wj * F_prev[y_current_prev, x_current_prev, 1]
                sum_wF2 += wj * F_prev[y_current_prev, x_current_prev, 2]
                sum_wB0 += wj * B_prev[y_current_prev, x_current_prev, 0]
                sum_wB1 += wj * B_prev[y_current_prev, x_current_prev, 1]
                sum_wB2 += wj * B_prev[y_current_prev, x_current_prev, 2]
            else:
                sum_wF0 += wj * F[y2, x, 0]
                sum_wF1 += wj * F[y2, x, 1]
                sum_wF2 += wj * F[y2, x, 2]
                sum_wB0 += wj * B[y2, x, 0]
                sum_wB1 += wj * B[y2, x, 1]
                sum_wB2 += wj * B[y2, x, 2]

            # Down neighbor.
            wj = neighbor_weights[y, x, 3]
            y2 = y_down
            if y2 == y:
                sum_wF0 += wj * F_prev[y_current_prev, x_current_prev, 0]
                sum_wF1 += wj * F_prev[y_current_prev, x_current_prev, 1]
                sum_wF2 += wj * F_prev[y_current_prev, x_current_prev, 2]
                sum_wB0 += wj * B_prev[y_current_prev, x_current_prev, 0]
                sum_wB1 += wj * B_prev[y_current_prev, x_current_prev, 1]
                sum_wB2 += wj * B_prev[y_current_prev, x_current_prev, 2]
            else:
                sum_wF0 += wj * F[y2, x, 0]
                sum_wF1 += wj * F[y2, x, 1]
                sum_wF2 += wj * F[y2, x, 2]
                sum_wB0 += wj * B[y2, x, 0]
                sum_wB1 += wj * B[y2, x, 1]
                sum_wB2 += wj * B[y2, x, 2]

            inv_W_local = inv_W[y, x]

            if a0 < 0.01 or a0 > 0.99:
                inv_Wp1_local = inv_Wp1[y, x]
                mu_F0 = sum_wF0 * inv_W_local
                mu_B0 = sum_wB0 * inv_W_local
                r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
                mu_F1 = sum_wF1 * inv_W_local
                mu_B1 = sum_wB1 * inv_W_local
                r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
                mu_F2 = sum_wF2 * inv_W_local
                mu_B2 = sum_wB2 * inv_W_local
                r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2
                if a0 < 0.01:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0 + r0 * inv_Wp1_local))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1 + r1 * inv_Wp1_local))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2 + r2 * inv_Wp1_local))
                else:
                    F[y, x, 0] = max(0.0, min(1.0, mu_F0 + r0 * inv_Wp1_local))
                    F[y, x, 1] = max(0.0, min(1.0, mu_F1 + r1 * inv_Wp1_local))
                    F[y, x, 2] = max(0.0, min(1.0, mu_F2 + r2 * inv_Wp1_local))
                    B[y, x, 0] = max(0.0, min(1.0, mu_B0))
                    B[y, x, 1] = max(0.0, min(1.0, mu_B1))
                    B[y, x, 2] = max(0.0, min(1.0, mu_B2))
                continue

            fg_g = fg_gain[y, x]
            bg_g = bg_gain[y, x]

            mu_F0 = sum_wF0 * inv_W_local
            mu_B0 = sum_wB0 * inv_W_local
            r0 = image[y, x, 0] - a0 * mu_F0 - a1 * mu_B0
            mu_F1 = sum_wF1 * inv_W_local
            mu_B1 = sum_wB1 * inv_W_local
            r1 = image[y, x, 1] - a0 * mu_F1 - a1 * mu_B1
            mu_F2 = sum_wF2 * inv_W_local
            mu_B2 = sum_wB2 * inv_W_local
            r2 = image[y, x, 2] - a0 * mu_F2 - a1 * mu_B2

            F[y, x, 0] = max(0.0, min(1.0, mu_F0 + fg_g * r0))
            F[y, x, 1] = max(0.0, min(1.0, mu_F1 + fg_g * r1))
            F[y, x, 2] = max(0.0, min(1.0, mu_F2 + fg_g * r2))
            B[y, x, 0] = max(0.0, min(1.0, mu_B0 + bg_g * r0))
            B[y, x, 1] = max(0.0, min(1.0, mu_B1 + bg_g * r1))
            B[y, x, 2] = max(0.0, min(1.0, mu_B2 + bg_g * r2))


@njit(cache=True, nogil=True, parallel=True)
def _build_level_coefficients(
    alpha,
    eps,
    omega,
    neighbor_weights,
    inv_W,
    inv_Wp1,
    fg_gain,
    bg_gain,
):
    h, w = alpha.shape
    for y in prange(h):
        for x in range(w):
            a0 = alpha[y, x]
            a1 = 1.0 - a0

            if 0 < x < w - 1 and 0 < y < h - 1:
                w0 = eps + omega * abs(a0 - alpha[y, x - 1])
                w1 = eps + omega * abs(a0 - alpha[y, x + 1])
                w2 = eps + omega * abs(a0 - alpha[y - 1, x])
                w3 = eps + omega * abs(a0 - alpha[y + 1, x])
            else:
                x_left = max(0, x - 1)
                x_right = min(w - 1, x + 1)
                y_up = max(0, y - 1)
                y_down = min(h - 1, y + 1)

                w0 = eps + omega * abs(a0 - alpha[y, x_left])
                w1 = eps + omega * abs(a0 - alpha[y, x_right])
                w2 = eps + omega * abs(a0 - alpha[y_up, x])
                w3 = eps + omega * abs(a0 - alpha[y_down, x])

            neighbor_weights[y, x, 0] = w0
            neighbor_weights[y, x, 1] = w1
            neighbor_weights[y, x, 2] = w2
            neighbor_weights[y, x, 3] = w3

            W = w0 + w1 + w2 + w3
            inv_W[y, x] = 1.0 / W
            inv_Wp1[y, x] = 1.0 / (W + 1.0)

            D = W + a0 * a0 + a1 * a1
            inv_D = 1.0 / D
            fg_gain[y, x] = a0 * inv_D
            bg_gain[y, x] = a1 * inv_D


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

        coeffs_w = np.empty((h, w, 4), dtype=np.float32)
        coeffs_inv_W = np.empty((h, w), dtype=np.float32)
        coeffs_inv_Wp1 = np.empty((h, w), dtype=np.float32)
        coeffs_fg_gain = np.empty((h, w), dtype=np.float32)
        coeffs_bg_gain = np.empty((h, w), dtype=np.float32)
        _build_level_coefficients(
            alpha,
            eps,
            omega,
            coeffs_w,
            coeffs_inv_W,
            coeffs_inv_Wp1,
            coeffs_fg_gain,
            coeffs_bg_gain,
        )

        if n_iter == 0:
            _resize_nearest_multichannel(F, F_prev)
            _resize_nearest_multichannel(B, B_prev)
        else:
            x_prev_map = _resize_index_map(F_prev.shape[1], w)
            y_prev_map = _resize_index_map(F_prev.shape[0], h)
            _update_rb_half_cached_from_prev_level(
                F,
                B,
                image,
                alpha,
                coeffs_w,
                coeffs_inv_W,
                coeffs_inv_Wp1,
                coeffs_fg_gain,
                coeffs_bg_gain,
                F_prev,
                B_prev,
                x_prev_map,
                y_prev_map,
                h,
                w,
            )
            _update_rb_half_cached_from_prev_level_with_boundary_fallback(
                F,
                B,
                image,
                alpha,
                coeffs_w,
                coeffs_inv_W,
                coeffs_inv_Wp1,
                coeffs_fg_gain,
                coeffs_bg_gain,
                F_prev,
                B_prev,
                x_prev_map,
                y_prev_map,
                h,
                w,
            )
            for _i_iter in range(1, n_iter):
                _update_rb_half_cached(
                    F,
                    B,
                    image,
                    alpha,
                    coeffs_w,
                    coeffs_inv_W,
                    coeffs_inv_Wp1,
                    coeffs_fg_gain,
                    coeffs_bg_gain,
                    h,
                    w,
                    0,
                )
                _update_rb_half_cached(
                    F,
                    B,
                    image,
                    alpha,
                    coeffs_w,
                    coeffs_inv_W,
                    coeffs_inv_Wp1,
                    coeffs_fg_gain,
                    coeffs_bg_gain,
                    h,
                    w,
                    1,
                )

        F_prev = F
        B_prev = B

    return F_prev, B_prev
