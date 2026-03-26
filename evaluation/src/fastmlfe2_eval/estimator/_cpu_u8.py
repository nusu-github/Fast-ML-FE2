from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

from fastmlfe2_eval.estimator._cpu_impl import estimate_fb_ml_u8 as _estimate_fb_ml_u8

if TYPE_CHECKING:
    from numpy.typing import NDArray

    from fastmlfe2_eval.estimator._types import EstimatorParams

__all__ = ["estimate_fb_ml"]


def estimate_fb_ml(
    input_image: NDArray[np.uint8],
    input_alpha: NDArray[np.uint8],
    params: EstimatorParams,
) -> tuple[NDArray[np.uint8], NDArray[np.uint8]]:
    if input_image.ndim != 3 or input_image.shape[2] != 3:
        msg = f"image must be h×w×3, got shape {input_image.shape}"
        raise ValueError(msg)
    if input_alpha.ndim != 2:
        msg = f"alpha must be h×w, got shape {input_alpha.shape}"
        raise ValueError(msg)
    if input_image.shape[:2] != input_alpha.shape:
        msg = f"shape mismatch: image {input_image.shape[:2]} vs alpha {input_alpha.shape}"
        raise ValueError(msg)
    if input_image.dtype != np.uint8:
        msg = f"cpu_u8 backend requires uint8 image, got dtype {input_image.dtype}"
        raise ValueError(msg)
    if input_alpha.dtype != np.uint8:
        msg = f"cpu_u8 backend requires uint8 alpha, got dtype {input_alpha.dtype}"
        raise ValueError(msg)

    image_u8 = np.ascontiguousarray(input_image, dtype=np.uint8)
    alpha_u8 = np.ascontiguousarray(input_alpha, dtype=np.uint8)

    foreground = np.empty_like(image_u8, dtype=np.uint8)
    background = np.empty_like(image_u8, dtype=np.uint8)
    _estimate_fb_ml_u8(
        foreground,
        background,
        image_u8,
        alpha_u8,
        np.float32(params.regularization),
        np.float32(params.gradient_weight),
        int(params.n_small_iterations),
        int(params.n_big_iterations),
        int(params.small_size),
    )
    return foreground, background
