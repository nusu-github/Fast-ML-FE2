from __future__ import annotations

import importlib.util
from pathlib import Path


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
