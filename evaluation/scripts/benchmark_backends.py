from __future__ import annotations

import argparse
import statistics as stats
import time
from collections.abc import Callable
from typing import NamedTuple

import numpy as np

from fastmlfe2_eval.estimator import estimate_foreground
from fastmlfe2_eval.metrics import gradient_error, mse_error, sad_error
from fastmlfe2_eval.patterns import make_pattern_case

INV_255 = 1.0 / 255.0

try:
    import cupy  # noqa: F401

    HAS_CUPY = True
except Exception:
    HAS_CUPY = False


class BenchmarkTarget(NamedTuple):
    input_kind: str
    runner: Callable[[np.ndarray, np.ndarray], tuple[np.ndarray, np.ndarray]]


def to_float32(image_u8: np.ndarray, alpha_u8: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    return image_u8.astype(np.float32) * INV_255, alpha_u8.astype(np.float32) * INV_255


def run_fastmlfe_backend(
    backend: str,
) -> Callable[[np.ndarray, np.ndarray], tuple[np.ndarray, np.ndarray]]:
    def run(image: np.ndarray, alpha: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        return estimate_foreground(image, alpha, backend=backend, return_background=True)

    return run


def run_pymatting_ml(image: np.ndarray, alpha: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    from pymatting.foreground.estimate_foreground_ml import estimate_foreground_ml

    return estimate_foreground_ml(image, alpha, return_background=True)


def run_pymatting_ml_cupy(image: np.ndarray, alpha: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    from pymatting.foreground.estimate_foreground_ml_cupy import estimate_foreground_ml_cupy

    return estimate_foreground_ml_cupy(image, alpha, return_background=True)


def run_pymatting_cf(image: np.ndarray, alpha: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    from pymatting.foreground.estimate_foreground_cf import estimate_foreground_cf

    return estimate_foreground_cf(image, alpha, return_background=True)


def build_benchmark_targets(*, include_cf: bool = False) -> dict[str, BenchmarkTarget]:
    targets = {
        "cpu": BenchmarkTarget("f32", run_fastmlfe_backend("cpu")),
        "cpu_u8": BenchmarkTarget("u8", run_fastmlfe_backend("cpu_u8")),
        "cpu_fx_u8": BenchmarkTarget("u8", run_fastmlfe_backend("cpu_fx_u8")),
        "pymatting_ml": BenchmarkTarget("f32", run_pymatting_ml),
    }
    if include_cf:
        targets["pymatting_cf"] = BenchmarkTarget("f32", run_pymatting_cf)
    if HAS_CUPY:
        targets["gpu"] = BenchmarkTarget("f32", run_fastmlfe_backend("gpu"))
        targets["pymatting_ml_cupy"] = BenchmarkTarget("f32", run_pymatting_ml_cupy)
    return targets


def detect_spike(times: list[float]) -> bool:
    if len(times) < 4:
        return False
    median = stats.median(times)
    q1 = stats.quantiles(times, n=4)[0]
    q3 = stats.quantiles(times, n=4)[2]
    iqr = q3 - q1
    return max(times) > median * 1.20 or (iqr > 0.0 and max(times) > q3 + 1.5 * iqr)


def timed_batch(
    image: np.ndarray,
    alpha: np.ndarray,
    name: str,
    runner: Callable[[np.ndarray, np.ndarray], tuple[np.ndarray, np.ndarray]],
    repeats: int,
    idle_seconds: int,
) -> tuple[list[float], tuple[np.ndarray, np.ndarray]]:
    runner(image, alpha)
    print(f"[{name}] warmup complete; idling for {idle_seconds}s before timing...", flush=True)
    time.sleep(idle_seconds)

    timings: list[float] = []
    first_result: tuple[np.ndarray, np.ndarray] | None = None
    for i in range(repeats):
        t0 = time.perf_counter()
        result = runner(image, alpha)
        elapsed = time.perf_counter() - t0
        timings.append(elapsed)
        if first_result is None:
            first_result = result
        print(f"[{name}] run {i + 1}/{repeats}: {elapsed:.6f}s", flush=True)

    if detect_spike(timings):
        print(f"[{name}] spike detected; rerunning batch after idle period", flush=True)
        time.sleep(idle_seconds)
        timings = []
        first_result = None
        for i in range(repeats):
            t0 = time.perf_counter()
            result = runner(image, alpha)
            elapsed = time.perf_counter() - t0
            timings.append(elapsed)
            if first_result is None:
                first_result = result
            print(f"[{name}] rerun {i + 1}/{repeats}: {elapsed:.6f}s", flush=True)

    assert first_result is not None
    return timings, first_result


def summarize_times(name: str, timings: list[float]) -> None:
    mean = stats.mean(timings)
    median = stats.median(timings)
    std = stats.pstdev(timings) if len(timings) > 1 else 0.0
    print(f"[{name}] mean={mean:.6f}s median={median:.6f}s std={std:.6f}s", flush=True)


def _normalize_foreground(result: tuple[np.ndarray, np.ndarray]) -> np.ndarray:
    foreground, _background = result
    if np.issubdtype(foreground.dtype, np.integer):
        return foreground.astype(np.float32) * INV_255
    return foreground.astype(np.float32, copy=False)


def compare_backend_metrics(
    cpu_result: tuple[np.ndarray, np.ndarray],
    backend_result: tuple[np.ndarray, np.ndarray],
    weights: np.ndarray,
    mask: np.ndarray,
) -> dict[str, float]:
    cpu_foreground = _normalize_foreground(cpu_result)
    backend_foreground = _normalize_foreground(backend_result)
    return {
        "sad": sad_error(backend_foreground, cpu_foreground, weights, mask),
        "mse": mse_error(backend_foreground, cpu_foreground, weights, mask),
        "grad": gradient_error(backend_foreground, cpu_foreground, weights, mask),
    }


def print_backend_metrics(
    cpu_result: tuple[np.ndarray, np.ndarray],
    backend_result: tuple[np.ndarray, np.ndarray],
    weights: np.ndarray,
    mask: np.ndarray,
    label: str,
) -> None:
    metrics = compare_backend_metrics(cpu_result, backend_result, weights, mask)
    print(
        f"[{label} vs cpu] "
        f"SAD={metrics['sad']:.8f} "
        f"MSE={metrics['mse']:.8f} "
        f"GRAD={metrics['grad']:.8f}",
        flush=True,
    )


def parse_size(spec: str) -> tuple[int, int]:
    try:
        h_str, w_str = spec.lower().split("x", 1)
        h = int(h_str)
        w = int(w_str)
    except ValueError as exc:
        msg = f"invalid size spec {spec!r}; expected HxW"
        raise argparse.ArgumentTypeError(msg) from exc
    if h < 1 or w < 1:
        msg = f"size must be positive, got {spec!r}"
        raise argparse.ArgumentTypeError(msg)
    return h, w


DEFAULT_SIZES = [(1024, 1024), (1536, 1536)]


class BenchmarkArgumentParser(argparse.ArgumentParser):
    def parse_args(self, args=None, namespace=None):
        parsed = super().parse_args(args, namespace)
        if parsed.size is None:
            parsed.size = list(DEFAULT_SIZES)
        return parsed


def build_parser() -> argparse.ArgumentParser:
    parser = BenchmarkArgumentParser(description="Benchmark CPU float32, CPU u8, CPU fixed u8, and GPU backends.")
    parser.add_argument(
        "--size",
        action="append",
        type=parse_size,
        default=None,
        help="Synthetic benchmark size in HxW form. May be repeated.",
    )
    parser.add_argument("--repeats", type=int, default=7, help="Timed repeats per backend.")
    parser.add_argument("--idle-seconds", type=int, default=30, help="Idle time before timing.")
    parser.add_argument(
        "--pattern",
        choices=(
            "saturating_slab",
            "centered_vertical_step",
            "shifted_vertical_step_pair",
            "checkerboard",
        ),
        default="centered_vertical_step",
        help="Lean-backed synthetic pattern family.",
    )
    parser.add_argument(
        "--epsilon",
        type=float,
        default=1.0 / 255.0,
        help="Near-opaque epsilon for the saturating slab pattern.",
    )
    parser.add_argument(
        "--period",
        type=int,
        default=2,
        help="Checkerboard block period in pixels.",
    )
    parser.add_argument(
        "--include-cf",
        action="store_true",
        help="Include PyMatting closed-form estimation in addition to the default multilevel comparisons.",
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    targets = build_benchmark_targets(include_cf=args.include_cf)

    for index, (h, w) in enumerate(args.size):
        print(f"\n=== synthetic pattern {args.pattern} {h}x{w} ===", flush=True)
        kwargs: dict[str, float | int] = {}
        if args.pattern == "saturating_slab":
            kwargs["epsilon"] = args.epsilon
        if args.pattern == "checkerboard":
            kwargs["period"] = args.period
        case = make_pattern_case(args.pattern, h, w, **kwargs)
        image_u8 = np.rint(case.image * 255.0).astype(np.uint8)
        alpha_u8 = np.rint(case.alpha * 255.0).astype(np.uint8)
        image_f32, alpha_f32 = to_float32(image_u8, alpha_u8)
        inputs = {
            "f32": (image_f32, alpha_f32),
            "u8": (image_u8, alpha_u8),
        }
        benchmark_times: dict[str, list[float]] = {}
        benchmark_results: dict[str, tuple[np.ndarray, np.ndarray]] = {}

        for name, target in targets.items():
            image, alpha = inputs[target.input_kind]
            try:
                timings, result = timed_batch(
                    image,
                    alpha,
                    name,
                    target.runner,
                    args.repeats,
                    args.idle_seconds,
                )
            except Exception as exc:
                print(f"[{name}] benchmark skipped: {exc!r}", flush=True)
                continue
            benchmark_times[name] = timings
            benchmark_results[name] = result
            summarize_times(name, timings)

        cpu_result = benchmark_results["cpu"]
        cpu_times = benchmark_times["cpu"]

        for name, result in benchmark_results.items():
            if name == "cpu":
                continue
            print_backend_metrics(cpu_result, result, case.weights, case.mask, name)

        if "gpu" not in targets:
            print("[gpu] CuPy unavailable; GPU benchmark skipped", flush=True)

        for name, timings in benchmark_times.items():
            if name == "cpu":
                continue
            print(
                f"[speed] {name}/cpu mean ratio="
                f"{stats.mean(timings) / stats.mean(cpu_times):.3f}x "
                f"(>1.0 means {name} is slower)",
                flush=True,
            )
        if "cpu_u8" in benchmark_times and "cpu_fx_u8" in benchmark_times:
            print(
                f"[speed] cpu_fx_u8/cpu_u8 mean ratio="
                f"{stats.mean(benchmark_times['cpu_fx_u8']) / stats.mean(benchmark_times['cpu_u8']):.3f}x "
                f"(>1.0 means cpu_fx_u8 is slower)",
                flush=True,
            )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
