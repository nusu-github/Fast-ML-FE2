"""Lean-backed synthetic pattern families for evaluation and benchmarking."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class PatternCase:
    """Full synthetic case usable for both metrics and estimator benchmarks."""

    name: str
    image: np.ndarray
    alpha: np.ndarray
    reference_fg: np.ndarray
    probe_fg: np.ndarray
    weights: np.ndarray
    mask: np.ndarray
    metadata: dict[str, int | float | str]


def _validate_shape(h: int, w: int) -> None:
    if h < 1 or w < 1:
        msg = f"pattern dimensions must be positive, got {h}x{w}"
        raise ValueError(msg)


def _validate_unit_interval(name: str, value: float) -> np.float32:
    if not 0.0 <= value <= 1.0:
        msg = f"{name} must lie in [0, 1], got {value}"
        raise ValueError(msg)
    return np.float32(value)


def _make_case(
    *,
    name: str,
    reference_fg: np.ndarray,
    probe_fg: np.ndarray,
    weights: np.ndarray,
    metadata: dict[str, int | float | str],
) -> PatternCase:
    alpha = np.asarray(weights, dtype=np.float32)
    mask = np.ones(alpha.shape, dtype=bool)
    image = alpha[:, :, np.newaxis] * np.asarray(reference_fg, dtype=np.float32)
    return PatternCase(
        name=name,
        image=image.astype(np.float32, copy=False),
        alpha=alpha,
        reference_fg=np.asarray(reference_fg, dtype=np.float32),
        probe_fg=np.asarray(probe_fg, dtype=np.float32),
        weights=alpha,
        mask=mask,
        metadata=metadata,
    )


def make_saturating_slab_case(
    h: int,
    w: int,
    *,
    epsilon: float = 1.0 / 255.0,
    fg_value: float = 0.0,
    probe_value: float = 1.0,
) -> PatternCase:
    """Uniform near-opaque slab that nearly maximizes SAD/MSE."""
    _validate_shape(h, w)
    if not 0.0 < epsilon < 1.0:
        msg = f"epsilon must lie in (0, 1), got {epsilon}"
        raise ValueError(msg)
    fg = _validate_unit_interval("fg_value", fg_value)
    probe = _validate_unit_interval("probe_value", probe_value)
    reference_fg = np.full((h, w, 3), fg, dtype=np.float32)
    probe_fg = np.full((h, w, 3), probe, dtype=np.float32)
    weights = np.full((h, w), 1.0 - epsilon, dtype=np.float32)
    return _make_case(
        name="saturating_slab",
        reference_fg=reference_fg,
        probe_fg=probe_fg,
        weights=weights,
        metadata={"epsilon": float(epsilon), "fg_value": float(fg), "probe_value": float(probe)},
    )


def make_centered_vertical_step_case(
    h: int,
    w: int,
    *,
    step_col: int | None = None,
    low: float = 0.0,
    high: float = 1.0,
    alpha_value: float = 1.0,
) -> PatternCase:
    """Vertical step edge against a flat probe image."""
    _validate_shape(h, w)
    step_col = w // 2 if step_col is None else step_col
    if not 0 <= step_col <= w:
        msg = f"step_col must lie in [0, {w}], got {step_col}"
        raise ValueError(msg)
    low_value = _validate_unit_interval("low", low)
    high_value = _validate_unit_interval("high", high)
    alpha = _validate_unit_interval("alpha_value", alpha_value)
    reference_fg = np.full((h, w, 3), high_value, dtype=np.float32)
    reference_fg[:, :step_col, :] = low_value
    probe_fg = np.full((h, w, 3), low_value, dtype=np.float32)
    weights = np.full((h, w), alpha, dtype=np.float32)
    return _make_case(
        name="centered_vertical_step",
        reference_fg=reference_fg,
        probe_fg=probe_fg,
        weights=weights,
        metadata={"step_col": step_col, "low": float(low_value), "high": float(high_value)},
    )


def make_shifted_vertical_step_pair_case(
    h: int,
    w: int,
    *,
    left_step_col: int | None = None,
    right_step_col: int | None = None,
    low: float = 0.0,
    high: float = 1.0,
    alpha_value: float = 1.0,
) -> PatternCase:
    """Two equal-contrast vertical steps at different positions."""
    _validate_shape(h, w)
    left = w // 2 if left_step_col is None else left_step_col
    right = min(w - 1, left + 1) if right_step_col is None else right_step_col
    if not 0 <= left <= w:
        msg = f"left_step_col must lie in [0, {w}], got {left}"
        raise ValueError(msg)
    if not 0 <= right <= w:
        msg = f"right_step_col must lie in [0, {w}], got {right}"
        raise ValueError(msg)
    if left == right:
        msg = "left_step_col and right_step_col must differ"
        raise ValueError(msg)
    low_value = _validate_unit_interval("low", low)
    high_value = _validate_unit_interval("high", high)
    alpha = _validate_unit_interval("alpha_value", alpha_value)
    reference_fg = np.full((h, w, 3), high_value, dtype=np.float32)
    reference_fg[:, :left, :] = low_value
    probe_fg = np.full((h, w, 3), high_value, dtype=np.float32)
    probe_fg[:, :right, :] = low_value
    weights = np.full((h, w), alpha, dtype=np.float32)
    return _make_case(
        name="shifted_vertical_step_pair",
        reference_fg=reference_fg,
        probe_fg=probe_fg,
        weights=weights,
        metadata={
            "left_step_col": left,
            "right_step_col": right,
            "low": float(low_value),
            "high": float(high_value),
        },
    )


def make_checkerboard_case(
    h: int,
    w: int,
    *,
    period: int = 2,
    phase_x: int = 0,
    phase_y: int = 0,
    low: float = 0.0,
    high: float = 1.0,
    alpha_value: float = 1.0,
) -> PatternCase:
    """High-frequency checkerboard against a flat probe image."""
    _validate_shape(h, w)
    if period < 1:
        msg = f"period must be positive, got {period}"
        raise ValueError(msg)
    low_value = _validate_unit_interval("low", low)
    high_value = _validate_unit_interval("high", high)
    alpha = _validate_unit_interval("alpha_value", alpha_value)
    yy, xx = np.mgrid[0:h, 0:w]
    board = (((xx + phase_x) // period + (yy + phase_y) // period) % 2).astype(np.float32)
    board_rgb = np.repeat(board[:, :, np.newaxis], 3, axis=2)
    reference_fg = np.where(board_rgb > 0.5, high_value, low_value).astype(np.float32)
    probe_fg = np.full((h, w, 3), low_value, dtype=np.float32)
    weights = np.full((h, w), alpha, dtype=np.float32)
    return _make_case(
        name="checkerboard",
        reference_fg=reference_fg,
        probe_fg=probe_fg,
        weights=weights,
        metadata={
            "period": period,
            "phase_x": phase_x,
            "phase_y": phase_y,
            "low": float(low_value),
            "high": float(high_value),
        },
    )


def list_pattern_families() -> tuple[str, ...]:
    """Return the public Lean-backed pattern family names."""
    return (
        "saturating_slab",
        "centered_vertical_step",
        "shifted_vertical_step_pair",
        "checkerboard",
    )


def make_pattern_case(name: str, h: int, w: int, **kwargs) -> PatternCase:
    """Dispatch to a named Lean-backed pattern family."""
    match name:
        case "saturating_slab":
            return make_saturating_slab_case(h, w, **kwargs)
        case "centered_vertical_step":
            return make_centered_vertical_step_case(h, w, **kwargs)
        case "shifted_vertical_step_pair":
            return make_shifted_vertical_step_pair_case(h, w, **kwargs)
        case "checkerboard":
            return make_checkerboard_case(h, w, **kwargs)
        case _:
            available = ", ".join(list_pattern_families())
            msg = f"unknown pattern family {name!r}; expected one of {available}"
            raise ValueError(msg)
