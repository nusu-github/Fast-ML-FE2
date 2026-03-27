from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

from fastmlfe2_eval.estimator import _cpu_impl

if TYPE_CHECKING:
    from numpy.typing import NDArray

    from fastmlfe2_eval.estimator._types import EstimatorParams

_build_level_solver_coefficients = _cpu_impl._build_level_solver_coefficients
_resize_nearest_rgb = _cpu_impl._resize_nearest_rgb
_resize_nearest_scalar = _cpu_impl._resize_nearest_scalar
_update_red_black_half_step = _cpu_impl._update_red_black_half_step
_update_red_black_half_step_from_previous_level = (
    _cpu_impl._update_red_black_half_step_from_previous_level
)
_update_red_black_half_step_from_previous_level_with_boundary_fallback = (
    _cpu_impl._update_red_black_half_step_from_previous_level_with_boundary_fallback
)
_estimate_multilevel_foreground_background = _cpu_impl.estimate_multilevel_foreground_background

__all__ = [
    "estimate_multilevel_foreground_background",
    "prepare_cpu_estimator_inputs",
]


def _resize_index_map(src_size: int, dst_size: int) -> np.ndarray:
    coords = np.arange(dst_size, dtype=np.int32)
    return np.minimum(src_size - 1, coords * src_size // dst_size).astype(np.int32)


def _require_cpu_float32_c_contiguous(
    input_image: NDArray[np.floating],
    input_alpha: NDArray[np.floating],
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    if input_image.dtype != np.float32 or input_alpha.dtype != np.float32:
        msg = "cpu backend requires float32 image and alpha inputs"
        raise ValueError(msg)
    if not input_image.flags.c_contiguous or not input_alpha.flags.c_contiguous:
        msg = "cpu backend requires C-contiguous image and alpha inputs"
        raise ValueError(msg)
    return input_image, input_alpha


def prepare_cpu_estimator_inputs(
    input_image: NDArray[np.floating],
    input_alpha: NDArray[np.floating],
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    return (
        np.ascontiguousarray(input_image, dtype=np.float32),
        np.ascontiguousarray(input_alpha, dtype=np.float32),
    )


def estimate_multilevel_foreground_background(
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

    image_f32, alpha_f32 = _require_cpu_float32_c_contiguous(input_image, input_alpha)

    foreground = np.empty_like(image_f32, dtype=np.float32)
    background = np.empty_like(image_f32, dtype=np.float32)
    _estimate_multilevel_foreground_background(
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
