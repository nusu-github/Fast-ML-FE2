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
) -> (
    NDArray[np.float32]
    | NDArray[np.uint8]
    | tuple[NDArray[np.float32], NDArray[np.float32]]
    | tuple[NDArray[np.uint8], NDArray[np.uint8]]
):
    if image.ndim != 3 or image.shape[2] != 3:
        msg = f"image must be h×w×3, got shape {image.shape}"
        raise ValueError(msg)
    if alpha.ndim != 2:
        msg = f"alpha must be h×w, got shape {alpha.shape}"
        raise ValueError(msg)
    if image.shape[:2] != alpha.shape:
        msg = f"shape mismatch: image {image.shape[:2]} vs alpha {alpha.shape}"
        raise ValueError(msg)

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
        image_f32 = np.ascontiguousarray(image, dtype=np.float32)
        alpha_f32 = np.ascontiguousarray(alpha, dtype=np.float32)
        from fastmlfe2_eval.estimator._cpu import estimate_fb_ml

        foreground, background = estimate_fb_ml(image_f32, alpha_f32, params)
    elif backend == "cpu_u8":
        from fastmlfe2_eval.estimator._cpu_u8 import estimate_fb_ml

        foreground, background = estimate_fb_ml(image, alpha, params)
    elif backend == "gpu":
        image_f32 = np.ascontiguousarray(image, dtype=np.float32)
        alpha_f32 = np.ascontiguousarray(alpha, dtype=np.float32)
        try:
            from fastmlfe2_eval.estimator._gpu import estimate_fb_ml
        except ImportError:
            msg = "backend='gpu' requires CuPy (pip install cupy-cuda12x)"
            raise RuntimeError(msg) from None

        foreground, background = estimate_fb_ml(image_f32, alpha_f32, params)
    else:
        msg = f"unknown backend: {backend!r}, expected 'auto', 'cpu', 'cpu_u8', or 'gpu'"
        raise ValueError(msg)

    if return_background:
        return foreground, background
    return foreground
