import pytest

from fastmlfe2_eval.metrics import gradient_error, mse_error, sad_error
from fastmlfe2_eval.patterns import (
    make_centered_vertical_step_case,
    make_checkerboard_case,
    make_saturating_slab_case,
    make_shifted_vertical_step_pair_case,
)


def test_sad_zero_for_identical():
    case = make_saturating_slab_case(8, 8)
    assert sad_error(case.reference_fg, case.reference_fg, case.weights, case.mask) == 0.0


def test_mse_zero_for_identical():
    case = make_saturating_slab_case(8, 8)
    assert mse_error(case.reference_fg, case.reference_fg, case.weights, case.mask) == 0.0


def test_gradient_error_zero_for_identical():
    case = make_centered_vertical_step_case(32, 32)
    assert gradient_error(case.reference_fg, case.reference_fg, case.weights, case.mask) == 0.0


def test_saturating_slab_matches_sad_near_supremum_formula():
    epsilon = 1.0 / 255.0
    case = make_saturating_slab_case(8, 10, epsilon=epsilon)
    actual = sad_error(case.probe_fg, case.reference_fg, case.weights, case.mask)
    expected = 3.0 * 8 * 10 * (1.0 - epsilon)
    assert actual == pytest.approx(expected)


def test_saturating_slab_matches_mean_mse_formula():
    epsilon = 1.0 / 255.0
    case = make_saturating_slab_case(8, 10, epsilon=epsilon)
    actual = mse_error(case.probe_fg, case.reference_fg, case.weights, case.mask)
    assert actual == pytest.approx(1.0 - epsilon)


def test_gradient_error_positive_for_centered_vertical_step():
    case = make_centered_vertical_step_case(32, 32)
    assert gradient_error(case.probe_fg, case.reference_fg, case.weights, case.mask) > 1e-12


def test_gradient_error_positive_for_shifted_vertical_step_pair():
    case = make_shifted_vertical_step_pair_case(32, 32)
    assert gradient_error(case.probe_fg, case.reference_fg, case.weights, case.mask) > 1e-12


def test_gradient_error_positive_for_checkerboard():
    case = make_checkerboard_case(32, 32)
    assert gradient_error(case.probe_fg, case.reference_fg, case.weights, case.mask) > 1e-12
