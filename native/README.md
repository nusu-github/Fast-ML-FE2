# Native C++ FFI

This directory contains the C++ implementation backing the `FastMLFE2.NativeFFI` Lean module.
All functions are called through Lean's `@[extern]` mechanism.

## Files

| File                     | Purpose                                                 |
| ------------------------ | ------------------------------------------------------- |
| `fastmlfe2_ffi.h`        | Public C interface (status codes, function signatures)  |
| `fastmlfe2_ffi.cpp`      | Reference implementation of refinement, resize, clamp   |
| `lean_fastmlfe2_ffi.cpp` | Lean FFI wrappers (`lean_fastmlfe2_*` extern functions) |
| `smoke.cpp`              | Pure C++ unit tests for the FFI functions               |
| `runner.cpp`             | Standalone PGM-based refinement runner                  |

## Dependencies

- **OpenCV 4** — image I/O (`imread`/`imwrite`) and resize (`cv::resize`). Detected via
  `pkg-config --cflags --libs opencv4`.
- **Lean headers** — obtained from `lean --print-prefix` at build time.
- **g++** with `-std=c++17`.

## Data Model

`GrayImageHandle` (defined in `lean_fastmlfe2_ffi.cpp`) wraps a contiguous `std::vector<float>`
with width, height, and stride. It is registered as a Lean external class with garbage
collection support.

On the Lean side, `NativeGrayImage` is an opaque type. `NativeRgbImage` is a Lean structure
holding three `NativeGrayImage` channels (red, green, blue).

## Key FFI Functions

### Image Management

- `lean_fastmlfe2_gray_image_of_float_array` — create image from Lean `FloatArray`
- `lean_fastmlfe2_gray_image_to_float_array` — extract to Lean `FloatArray`
- `lean_fastmlfe2_gray_image_width` / `height` — dimension accessors

### Resize

- `lean_fastmlfe2_gray_image_resize` — bilinear/area interpolation via OpenCV
- `lean_fastmlfe2_gray_image_resize_nearest` — nearest-neighbor resize

### Refinement

- `lean_fastmlfe2_gray_image_reference_refine_single_pass` — single-pass grayscale
  four-neighbor refinement (one iteration)
- `lean_fastmlfe2_rgb_image_reference_refine` — multi-iteration RGB refinement
  (three channels, simultaneous update)

### Utility

- `lean_fastmlfe2_gray_image_clamp01` — in-place clamp to [0, 1]

### PNG I/O

- `lean_fastmlfe2_gray_image_read_png_gray` / `write_png_gray`
- `lean_fastmlfe2_gray_image_read_png_rgb_channel` / `write_png_rgb`

## Refinement Algorithm

The core refinement (`fastmlfe2_reference_refine_gray_single_pass`) implements the local
equation solver for a single channel:

1. For each pixel, compute four-neighbor weights: `w_j = ε_r + ω · |α_center − α_neighbor|`.
2. Compute weighted means of neighbor foreground/background values.
3. Solve the 2×2 normal equation per pixel (explicit inverse formula).
4. Write updated foreground and background to output buffers.

The RGB variant (`fastmlfe2_reference_refine_rgb`) applies this per-channel with a shared
alpha map, iterating for a configurable number of passes with clamp-after-each-pass.

## Build

All native targets are built automatically by `lake build`:

```sh
# Build the FFI static library (linked into Lean executables)
lake build

# Build the pure-C++ smoke test
lake build ffiSmoke
.lake/build/bin/ffi-smoke

# Build the PGM-based runner
lake build ffiRunner
.lake/build/bin/ffi-runner image.pgm alpha.pgm fg.pgm bg.pgm out_fg.pgm out_bg.pgm 10 0.00001 1.0
```

## Status Codes

The C interface returns `fastmlfe2_status` codes:

| Code                           | Meaning                       |
| ------------------------------ | ----------------------------- |
| `FASTMLFE2_OK`                 | Success                       |
| `FASTMLFE2_NULL_POINTER`       | Null buffer argument          |
| `FASTMLFE2_INVALID_DIMENSIONS` | Zero or mismatched dimensions |
| `FASTMLFE2_INVALID_STRIDE`     | Stride smaller than width     |
| `FASTMLFE2_INVALID_PARAMS`     | Invalid ε_r or ω              |
| `FASTMLFE2_ALIASING`           | Input/output buffers overlap  |
