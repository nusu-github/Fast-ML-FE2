from __future__ import annotations

import numpy as np
import pytest

from fastmlfe2_eval.patterns import (
    PatternCase,
    list_pattern_families,
    make_centered_vertical_step_case,
    make_checkerboard_case,
    make_pattern_case,
    make_saturating_slab_case,
    make_shifted_vertical_step_pair_case,
)


@pytest.mark.parametrize(
    ("name", "factory"),
    [
        ("saturating_slab", lambda: make_saturating_slab_case(16, 12)),
        ("centered_vertical_step", lambda: make_centered_vertical_step_case(16, 12)),
        ("shifted_vertical_step_pair", lambda: make_shifted_vertical_step_pair_case(16, 12)),
        ("checkerboard", lambda: make_checkerboard_case(16, 12)),
    ],
)
def test_pattern_factories_return_full_cases(name: str, factory):
    case = factory()

    assert isinstance(case, PatternCase)
    assert case.name == name
    assert case.image.shape == (16, 12, 3)
    assert case.alpha.shape == (16, 12)
    assert case.reference_fg.shape == (16, 12, 3)
    assert case.probe_fg.shape == (16, 12, 3)
    assert case.weights.shape == (16, 12)
    assert case.mask.shape == (16, 12)
    assert case.image.dtype == np.float32
    assert case.alpha.dtype == np.float32
    assert case.reference_fg.dtype == np.float32
    assert case.probe_fg.dtype == np.float32
    assert case.weights.dtype == np.float32
    assert case.mask.dtype == np.bool_


def test_pattern_registry_lists_all_lean_backed_families():
    assert list_pattern_families() == (
        "saturating_slab",
        "centered_vertical_step",
        "shifted_vertical_step_pair",
        "checkerboard",
    )


def test_make_pattern_case_dispatches():
    case = make_pattern_case("checkerboard", 16, 12, period=3)

    assert case.name == "checkerboard"
    assert case.metadata["period"] == 3
