from __future__ import annotations

import math
from dataclasses import dataclass
from typing import TYPE_CHECKING

import numpy as np

if TYPE_CHECKING:
    from numpy.typing import NDArray


@dataclass(frozen=True, slots=True)
class EstimatorParams:
    regularization: float = 5e-3
    gradient_weight: float = 0.1
    n_small_iterations: int = 10
    n_big_iterations: int = 2
    small_size: int = 32

    def __post_init__(self) -> None:
        if not math.isfinite(self.regularization) or self.regularization <= 0:
            msg = "regularization must be a finite positive value"
            raise ValueError(msg)


@dataclass(frozen=True, slots=True)
class LevelSpec:
    w: int
    h: int
    n_iter: int


def compute_level_schedule(w0: int, h0: int, params: EstimatorParams) -> list[LevelSpec]:
    if w0 <= 1 and h0 <= 1:
        n_iter = params.n_small_iterations
        return [LevelSpec(w=1, h=1, n_iter=n_iter)]

    n_levels = math.ceil(math.log2(max(w0, h0)))
    schedule: list[LevelSpec] = []
    for i_level in range(n_levels + 1):
        w = round(w0 ** (i_level / n_levels))
        h = round(h0 ** (i_level / n_levels))
        if w <= params.small_size and h <= params.small_size:
            n_iter = params.n_small_iterations
        else:
            n_iter = params.n_big_iterations
        schedule.append(LevelSpec(w=w, h=h, n_iter=n_iter))
    return schedule


def compute_initial_means(
    image: NDArray[np.float32], alpha: NDArray[np.float32]
) -> tuple[NDArray[np.float32], NDArray[np.float32]]:
    fg_mask = alpha > 0.9
    bg_mask = alpha < 0.1
    if fg_mask.any():
        fg_mean = image[fg_mask].mean(axis=0).astype(np.float32)
    else:
        fg_mean = np.zeros(3, dtype=np.float32)
    if bg_mask.any():
        bg_mean = image[bg_mask].mean(axis=0).astype(np.float32)
    else:
        bg_mean = np.zeros(3, dtype=np.float32)
    return fg_mean, bg_mean
