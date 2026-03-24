"""Error metrics for foreground estimation evaluation.

These metrics correspond to the quantities formalized in the Lean proofs:
- SAD: Sum of Absolute Differences
- MSE: Mean Squared Error
- GRAD: Gradient error (Gaussian-filtered, per Rhemann et al. 2009)
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np
from scipy.ndimage import correlate

if TYPE_CHECKING:
    from numpy.typing import NDArray


def sad_error(
    estimated: NDArray[np.floating],
    reference: NDArray[np.floating],
    weights: NDArray[np.floating],
    mask: NDArray[np.bool_],
) -> float:
    """Weighted sum of absolute differences on masked region."""
    diff = weights[:, :, np.newaxis] * np.abs(estimated - reference)
    return float(np.sum(diff[mask]))


def mse_error(
    estimated: NDArray[np.floating],
    reference: NDArray[np.floating],
    weights: NDArray[np.floating],
    mask: NDArray[np.bool_],
) -> float:
    """Weighted mean squared error on masked region."""
    diff = weights[:, :, np.newaxis] * np.square(estimated - reference)
    return float(np.mean(diff[mask]))


def _gaussian_gradient(image_2d: NDArray[np.floating], sigma: float) -> NDArray[np.floating]:
    """Gaussian-filtered gradient magnitude for a single channel."""
    r = int(3 * sigma)
    x = np.linspace(-r, r, 2 * r + 1)
    g = np.exp(-0.5 * np.square(x) / (sigma * sigma)) / (sigma * np.sqrt(2 * np.pi))
    dg = -x * g / (sigma**2)
    g /= np.linalg.norm(g)
    dg /= np.linalg.norm(dg)
    dx = correlate(correlate(image_2d, dg.reshape(1, -1)), g.reshape(-1, 1))
    dy = correlate(correlate(image_2d, dg.reshape(-1, 1)), g.reshape(1, -1))
    return np.sqrt(dx * dx + dy * dy)


def gradient_error(
    estimated: NDArray[np.floating],
    reference: NDArray[np.floating],
    weights: NDArray[np.floating],
    mask: NDArray[np.bool_],
    *,
    sigma: float = 1.4,
) -> float:
    """Gradient error across all channels (Rhemann et al. 2009)."""
    total = 0.0
    for c in range(estimated.shape[2]):
        g_est = _gaussian_gradient(estimated[:, :, c], sigma)
        g_ref = _gaussian_gradient(reference[:, :, c], sigma)
        diff = weights * np.square(g_est - g_ref)
        total += float(np.sum(diff[mask]))
    return total
