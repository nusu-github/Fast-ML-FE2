from __future__ import annotations

import argparse
import math
import statistics as stats
import time

import numpy as np

from fastmlfe2_eval.estimator import estimate_foreground

INV_255 = 1.0 / 255.0

try:
    import cupy  # noqa: F401

    HAS_CUPY = True
except Exception:
    HAS_CUPY = False


def make_quantized_pattern(h: int, w: int, seed: int) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    yy, xx = np.mgrid[0:h, 0:w]
    x = xx.astype(np.float32) / max(w - 1, 1)
    y = yy.astype(np.float32) / max(h - 1, 1)

    checker = ((xx // 37 + yy // 53) & 1).astype(np.float32)
    stripes = np.sin(2.0 * math.pi * (3.0 * x + 1.5 * y)).astype(np.float32)
    rings = np.cos(
        2.0 * math.pi * np.sqrt((x - 0.5) ** 2 + (y - 0.5) ** 2) * 4.0
    ).astype(np.float32)
    noise = rng.random((h, w), dtype=np.float32)

    image = np.stack(
        [
            0.12 + 0.70 * x + 0.10 * stripes + 0.08 * checker,
            0.08 + 0.72 * y + 0.08 * rings + 0.05 * noise,
            0.18 + 0.55 * (1.0 - x) * (1.0 - y) + 0.12 * np.sin(4.0 * math.pi * (x + y)),
        ],
        axis=2,
    )
    alpha = 0.5 + 0.35 * np.sin(5.0 * math.pi * (x + 0.2 * y)) * np.cos(
        3.0 * math.pi * (y - 0.3 * x)
    )
    alpha += 0.08 * checker - 0.04 * noise

    image = np.clip(image, 0.0, 1.0)
    alpha = np.clip(alpha, 0.0, 1.0)

    image_u8 = np.rint(image * 255.0).astype(np.uint8)
    alpha_u8 = np.rint(alpha * 255.0).astype(np.uint8)
    return image_u8, alpha_u8


def to_float32(image_u8: np.ndarray, alpha_u8: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    return image_u8.astype(np.float32) * INV_255, alpha_u8.astype(np.float32) * INV_255


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
    backend: str,
    repeats: int,
    idle_seconds: int,
) -> tuple[list[float], tuple[np.ndarray, np.ndarray]]:
    estimate_foreground(image, alpha, backend=backend, return_background=True)
    print(f"[{backend}] warmup complete; idling for {idle_seconds}s before timing...", flush=True)
    time.sleep(idle_seconds)

    timings: list[float] = []
    first_result: tuple[np.ndarray, np.ndarray] | None = None
    for i in range(repeats):
        t0 = time.perf_counter()
        result = estimate_foreground(image, alpha, backend=backend, return_background=True)
        elapsed = time.perf_counter() - t0
        timings.append(elapsed)
        if first_result is None:
            first_result = result
        print(f"[{backend}] run {i + 1}/{repeats}: {elapsed:.6f}s", flush=True)

    if detect_spike(timings):
        print(f"[{backend}] spike detected; rerunning batch after idle period", flush=True)
        time.sleep(idle_seconds)
        timings = []
        first_result = None
        for i in range(repeats):
            t0 = time.perf_counter()
            result = estimate_foreground(image, alpha, backend=backend, return_background=True)
            elapsed = time.perf_counter() - t0
            timings.append(elapsed)
            if first_result is None:
                first_result = result
            print(f"[{backend}] rerun {i + 1}/{repeats}: {elapsed:.6f}s", flush=True)

    assert first_result is not None
    return timings, first_result


def summarize_times(name: str, timings: list[float]) -> None:
    mean = stats.mean(timings)
    median = stats.median(timings)
    std = stats.pstdev(timings) if len(timings) > 1 else 0.0
    print(f"[{name}] mean={mean:.6f}s median={median:.6f}s std={std:.6f}s", flush=True)


def compare_cpu_and_u8_backend(
    cpu_result: tuple[np.ndarray, np.ndarray],
    u8_result: tuple[np.ndarray, np.ndarray],
    label: str,
) -> None:
    cpu_f, cpu_b = cpu_result
    u8_f, u8_b = u8_result
    u8_f32 = u8_f.astype(np.float32) * INV_255
    u8_b32 = u8_b.astype(np.float32) * INV_255
    abs_diff_f = np.abs(u8_f32 - cpu_f)
    abs_diff_b = np.abs(u8_b32 - cpu_b)
    mean_abs = float((abs_diff_f.mean() + abs_diff_b.mean()) / 2.0)
    max_abs = float(max(abs_diff_f.max(), abs_diff_b.max()))
    print(
        f"[{label} vs cpu] mean_abs={mean_abs:.8f} ({mean_abs * 255.0:.4f} LSB) "
        f"max_abs={max_abs:.8f} ({max_abs * 255.0:.4f} LSB)",
        flush=True,
    )


def compare_cpu_and_gpu(
    cpu_result: tuple[np.ndarray, np.ndarray],
    gpu_result: tuple[np.ndarray, np.ndarray],
) -> None:
    cpu_f, cpu_b = cpu_result
    gpu_f, gpu_b = gpu_result
    abs_diff_f = np.abs(cpu_f - gpu_f)
    abs_diff_b = np.abs(cpu_b - gpu_b)
    mean_abs = float((abs_diff_f.mean() + abs_diff_b.mean()) / 2.0)
    max_abs = float(max(abs_diff_f.max(), abs_diff_b.max()))
    print(
        f"[cpu vs gpu] mean_abs={mean_abs:.8f} ({mean_abs * 255.0:.4f} LSB) "
        f"max_abs={max_abs:.8f} ({max_abs * 255.0:.4f} LSB)",
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
    parser.add_argument("--seed", type=int, default=0, help="Base seed for synthetic patterns.")
    return parser


def main() -> int:
    args = build_parser().parse_args()

    for index, (h, w) in enumerate(args.size):
        print(f"\n=== synthetic pattern {h}x{w} ===", flush=True)
        image_u8, alpha_u8 = make_quantized_pattern(h, w, args.seed + index)
        image_f32, alpha_f32 = to_float32(image_u8, alpha_u8)

        cpu_times, cpu_result = timed_batch(
            image_f32,
            alpha_f32,
            "cpu",
            args.repeats,
            args.idle_seconds,
        )
        summarize_times("cpu", cpu_times)

        cpu_u8_times, cpu_u8_result = timed_batch(
            image_u8,
            alpha_u8,
            "cpu_u8",
            args.repeats,
            args.idle_seconds,
        )
        summarize_times("cpu_u8", cpu_u8_times)
        compare_cpu_and_u8_backend(cpu_result, cpu_u8_result, "cpu_u8")

        cpu_fx_u8_times, cpu_fx_u8_result = timed_batch(
            image_u8,
            alpha_u8,
            "cpu_fx_u8",
            args.repeats,
            args.idle_seconds,
        )
        summarize_times("cpu_fx_u8", cpu_fx_u8_times)
        compare_cpu_and_u8_backend(cpu_result, cpu_fx_u8_result, "cpu_fx_u8")

        if HAS_CUPY:
            try:
                gpu_times, gpu_result = timed_batch(
                    image_f32,
                    alpha_f32,
                    "gpu",
                    args.repeats,
                    args.idle_seconds,
                )
            except Exception as exc:
                print(f"[gpu] benchmark skipped: {exc!r}", flush=True)
            else:
                summarize_times("gpu", gpu_times)
                compare_cpu_and_gpu(cpu_result, gpu_result)
                print(
                    f"[speed] cpu_u8/cpu mean ratio="
                    f"{stats.mean(cpu_u8_times) / stats.mean(cpu_times):.3f}x "
                    f"(>1.0 means cpu_u8 is slower)",
                    flush=True,
                )
                print(
                    f"[speed] cpu_fx_u8/cpu mean ratio="
                    f"{stats.mean(cpu_fx_u8_times) / stats.mean(cpu_times):.3f}x "
                    f"(>1.0 means cpu_fx_u8 is slower)",
                    flush=True,
                )
                print(
                    f"[speed] cpu_fx_u8/cpu_u8 mean ratio="
                    f"{stats.mean(cpu_fx_u8_times) / stats.mean(cpu_u8_times):.3f}x "
                    f"(>1.0 means cpu_fx_u8 is slower)",
                    flush=True,
                )
                print(
                    f"[speed] cpu/gpu mean ratio="
                    f"{stats.mean(cpu_times) / stats.mean(gpu_times):.3f}x "
                    f"(>1.0 means gpu is faster)",
                    flush=True,
                )
        else:
            print("[gpu] CuPy unavailable; GPU benchmark skipped", flush=True)
            print(
                f"[speed] cpu_u8/cpu mean ratio="
                f"{stats.mean(cpu_u8_times) / stats.mean(cpu_times):.3f}x "
                f"(>1.0 means cpu_u8 is slower)",
                flush=True,
            )
            print(
                f"[speed] cpu_fx_u8/cpu mean ratio="
                f"{stats.mean(cpu_fx_u8_times) / stats.mean(cpu_times):.3f}x "
                f"(>1.0 means cpu_fx_u8 is slower)",
                flush=True,
            )
            print(
                f"[speed] cpu_fx_u8/cpu_u8 mean ratio="
                f"{stats.mean(cpu_fx_u8_times) / stats.mean(cpu_u8_times):.3f}x "
                f"(>1.0 means cpu_fx_u8 is slower)",
                flush=True,
            )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
