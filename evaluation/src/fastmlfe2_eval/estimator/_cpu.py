from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

from fastmlfe2_eval.estimator._cpu_impl import (
    _build_level_coefficients,
    _resize_nearest,
    _resize_nearest_multichannel,
    _update_rb_half_cached,
    _update_rb_half_cached_from_prev_level,
    _update_rb_half_cached_from_prev_level_with_boundary_fallback,
)
from fastmlfe2_eval.estimator._cpu_impl import (
    estimate_fb_ml as _estimate_fb_ml,
)

if TYPE_CHECKING:
    from numpy.typing import NDArray

    from fastmlfe2_eval.estimator._types import EstimatorParams

__all__ = [
    "_build_level_coefficients",
    "_resize_index_map",
    "_resize_nearest",
    "_resize_nearest_multichannel",
    "_update_rb_half_cached",
    "_update_rb_half_cached_from_prev_level",
    "_update_rb_half_cached_from_prev_level_with_boundary_fallback",
    "estimate_fb_ml",
]


def _resize_index_map(src_size: int, dst_size: int) -> np.ndarray:
    coords = np.arange(dst_size, dtype=np.int32)
    return np.minimum(src_size - 1, coords * src_size // dst_size).astype(np.int32)


def estimate_fb_ml(
    input_image: NDArray[np.floating],
    input_alpha: NDArray[np.floating],
    params: EstimatorParams,
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    if input_image.ndim != 3 or input_image.shape[2] != 3:
        msg = f"image must be h×w×3, got shape {input_image.shape}"
        raise ValueError(msg)
    if input_alpha.ndim != 2:
        msg = f"alpha must be h×w, got shape {input_alpha.shape}"
        raise ValueError(msg)
    if input_image.shape[:2] != input_alpha.shape:
        msg = f"shape mismatch: image {input_image.shape[:2]} vs alpha {input_alpha.shape}"
        raise ValueError(msg)

    image_f32 = np.ascontiguousarray(input_image, dtype=np.float32)
    alpha_f32 = np.ascontiguousarray(input_alpha, dtype=np.float32)

    foreground = np.empty_like(image_f32, dtype=np.float32)
    background = np.empty_like(image_f32, dtype=np.float32)
    _estimate_fb_ml(
        foreground,
        background,
        image_f32,
        alpha_f32,
        np.float32(params.regularization),
        np.float32(params.gradient_weight),
        int(params.n_small_iterations),
        int(params.n_big_iterations),
        int(params.small_size),
    )
    return foreground, background
