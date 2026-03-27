from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np
import pytest


_SCRIPT_PATH = Path(__file__).resolve().parents[1] / "scripts" / "benchmark_backends.py"
_SPEC = importlib.util.spec_from_file_location("benchmark_backends", _SCRIPT_PATH)
assert _SPEC is not None
assert _SPEC.loader is not None
benchmark_backends = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(benchmark_backends)


def test_explicit_sizes_replace_defaults():
    args = benchmark_backends.build_parser().parse_args(
        ["--size", "64x32", "--size", "128x96", "--repeats", "1", "--idle-seconds", "0"]
    )

    assert args.size == [(64, 32), (128, 96)]


def test_default_sizes_used_when_omitted():
    args = benchmark_backends.build_parser().parse_args(["--repeats", "1", "--idle-seconds", "0"])

    assert args.size == benchmark_backends.DEFAULT_SIZES


def test_default_pattern_used_when_omitted():
    args = benchmark_backends.build_parser().parse_args(["--repeats", "1", "--idle-seconds", "0"])

    assert args.pattern == "centered_vertical_step"


def test_explicit_pattern_is_parsed():
    args = benchmark_backends.build_parser().parse_args(
        ["--pattern", "checkerboard", "--repeats", "1", "--idle-seconds", "0"]
    )

    assert args.pattern == "checkerboard"


def test_compare_backend_metrics_zero_for_identical_foreground():
    foreground = np.zeros((8, 8, 3), dtype=np.float32)
    weights = np.ones((8, 8), dtype=np.float32)
    mask = np.ones((8, 8), dtype=bool)

    metrics = benchmark_backends.compare_backend_metrics(
        (foreground, foreground),
        (foreground, foreground),
        weights,
        mask,
    )

    assert metrics == {"sad": 0.0, "mse": 0.0, "grad": 0.0}


def test_compare_backend_metrics_positive_for_changed_foreground():
    reference = np.zeros((8, 8, 3), dtype=np.float32)
    candidate = np.full((8, 8, 3), 0.25, dtype=np.float32)
    weights = np.ones((8, 8), dtype=np.float32)
    mask = np.ones((8, 8), dtype=bool)

    metrics = benchmark_backends.compare_backend_metrics(
        (reference, reference),
        (candidate, candidate),
        weights,
        mask,
    )

    assert metrics["sad"] > 0.0
    assert metrics["mse"] > 0.0
    assert metrics["grad"] == pytest.approx(0.0, abs=1e-24)
