import numpy as np
import pytest

from fastmlfe2_eval.estimator._types import (
    EstimatorParams,
    compute_initial_means,
    compute_level_schedule,
)


def test_schedule_endpoints():
    schedule = compute_level_schedule(64, 32, EstimatorParams())
    assert schedule[0].w == 1 and schedule[0].h == 1
    assert schedule[-1].w == 64 and schedule[-1].h == 32


def test_schedule_monotone_growth():
    schedule = compute_level_schedule(640, 480, EstimatorParams())
    for i in range(1, len(schedule)):
        assert schedule[i].w >= schedule[i - 1].w
        assert schedule[i].h >= schedule[i - 1].h


def test_schedule_small_vs_big_iterations():
    params = EstimatorParams(n_small_iterations=10, n_big_iterations=2, small_size=32)
    schedule = compute_level_schedule(256, 256, params)
    for lvl in schedule:
        if lvl.w <= 32 and lvl.h <= 32:
            assert lvl.n_iter == 10
        else:
            assert lvl.n_iter == 2


def test_schedule_max_growth_factor():
    """Adjacent levels should grow by at most ~2x in each dimension."""
    schedule = compute_level_schedule(1024, 768, EstimatorParams())
    for i in range(1, len(schedule)):
        assert schedule[i].w <= 2 * schedule[i - 1].w + 1
        assert schedule[i].h <= 2 * schedule[i - 1].h + 1


def test_initial_means_pure_foreground():
    image = np.full((4, 4, 3), 0.5, dtype=np.float32)
    alpha = np.ones((4, 4), dtype=np.float32)
    fg, bg = compute_initial_means(image, alpha)
    np.testing.assert_allclose(fg, [0.5, 0.5, 0.5])
    np.testing.assert_allclose(bg, [0.0, 0.0, 0.0])


def test_initial_means_pure_background():
    image = np.full((4, 4, 3), 0.7, dtype=np.float32)
    alpha = np.zeros((4, 4), dtype=np.float32)
    fg, bg = compute_initial_means(image, alpha)
    np.testing.assert_allclose(fg, [0.0, 0.0, 0.0])
    np.testing.assert_allclose(bg, [0.7, 0.7, 0.7], rtol=1e-6)


def test_initial_means_mixed():
    rng = np.random.default_rng(42)
    image = rng.random((16, 16, 3)).astype(np.float32)
    alpha = rng.random((16, 16)).astype(np.float32)
    fg, bg = compute_initial_means(image, alpha)
    assert fg.shape == (3,) and fg.dtype == np.float32
    assert bg.shape == (3,) and bg.dtype == np.float32


def test_estimator_params_reject_nonpositive_regularization():
    with pytest.raises(ValueError, match="regularization must be a finite positive value"):
        EstimatorParams(regularization=0.0)


def test_schedule_1x1_image():
    """Edge case: 1×1 image should produce exactly 1 level."""
    schedule = compute_level_schedule(1, 1, EstimatorParams())
    assert len(schedule) == 1
    assert schedule[0].w == 1 and schedule[0].h == 1
