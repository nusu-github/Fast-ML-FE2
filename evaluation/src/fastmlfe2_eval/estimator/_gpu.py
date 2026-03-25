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

_ml_rb_half_kernel = cp.RawKernel(
    r"""
extern "C" __global__
void ml_rb_half(
    float *F,
    float *B,
    const float *image,
    const float *alpha,
    int w,
    int h,
    float regularization,
    float gradient_weight,
    int parity
){
    int x = blockDim.x * blockIdx.x + threadIdx.x;
    int y = blockDim.y * blockIdx.y + threadIdx.y;
    if (x >= w || y >= h) return;
    if (((x + y) & 1) != parity) return;

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
            sum_wF[c] += wj * F[j * 3 + c];
            sum_wB[c] += wj * B[j * 3 + c];
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
                F[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_F));
                B[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_B + r * inv_Wp1));
            } else {
                F[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_F + r * inv_Wp1));
                B[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_B));
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
        F[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_F + a0_inv_D * r));
        B[i * 3 + c] = fmaxf(0.0f, fminf(1.0f, mu_B + a1_inv_D * r));
    }
}
""",
    "ml_rb_half",
)

_BLOCK = (32, 32)


def _div_round_up(a: int, b: int) -> int:
    return (a + b - 1) // b


def _resize(dst, src, w_src, h_src, w_dst, h_dst, depth):
    grid = (_div_round_up(w_dst, _BLOCK[0]), _div_round_up(h_dst, _BLOCK[1]))
    _resize_nearest_kernel(grid, _BLOCK, (dst, src, w_src, h_src, w_dst, h_dst, depth))


def _run_red_black_sweep(F, B, image, alpha, w, h, eps, omega):
    grid = (_div_round_up(w, _BLOCK[0]), _div_round_up(h, _BLOCK[1]))
    _ml_rb_half_kernel(grid, _BLOCK, (F, B, image, alpha, w, h, eps, omega, 0))
    _ml_rb_half_kernel(grid, _BLOCK, (F, B, image, alpha, w, h, eps, omega, 1))


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

        if n_iter == 0:
            _resize(d_F, d_F_prev, w_prev, h_prev, w, h, 3)
            _resize(d_B, d_B_prev, w_prev, h_prev, w, h, 3)
        else:
            grid = (_div_round_up(w, _BLOCK[0]), _div_round_up(h, _BLOCK[1]))

            # First iteration: fused resize + iterate (reads from previous level's buffer)
            _ml_fused_resize_iterate_kernel(
                grid,
                _BLOCK,
                (
                    d_F,
                    d_B,
                    d_F_prev,
                    d_B_prev,
                    d_image_level,
                    d_alpha_level,
                    w,
                    h,
                    w_prev,
                    h_prev,
                    eps,
                    omega,
                ),
            )

            # Remaining iterations: in-place red-black sweeps.
            for _ in range(n_iter - 1):
                _run_red_black_sweep(d_F, d_B, d_image_level, d_alpha_level, w, h, eps, omega)

        d_F_prev, d_F = d_F, d_F_prev
        d_B_prev, d_B = d_B, d_B_prev

        # After loop: d_F_prev has the latest result
        w_prev, h_prev = w, h

    # d_F_prev has final result
    F_out = cp.asnumpy(d_F_prev[: h0 * w0 * 3].reshape(h0, w0, 3))
    B_out = cp.asnumpy(d_B_prev[: h0 * w0 * 3].reshape(h0, w0, 3))
    return F_out, B_out
