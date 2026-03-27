"""Evaluation harness for Fast-ML-FE2 proof implementations."""

from fastmlfe2_eval.estimator import estimate_foreground
from fastmlfe2_eval.metrics import gradient_error, mse_error, sad_error
from fastmlfe2_eval.patterns import (
    PatternCase,
    list_pattern_families,
    make_centered_vertical_step_case,
    make_checkerboard_case,
    make_pattern_case,
    make_saturating_slab_case,
    make_shifted_vertical_step_pair_case,
)

__all__ = [
    "PatternCase",
    "estimate_foreground",
    "gradient_error",
    "list_pattern_families",
    "make_centered_vertical_step_case",
    "make_checkerboard_case",
    "make_pattern_case",
    "make_saturating_slab_case",
    "make_shifted_vertical_step_pair_case",
    "mse_error",
    "sad_error",
]
