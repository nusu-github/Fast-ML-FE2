#pragma once

#include <nanobind/nanobind.h>
#include <nanobind/ndarray.h>
#include <nanobind/stl/vector.h>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

namespace nb = nanobind;

using Image = nb::ndarray<const float, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using MutableImage = nb::ndarray<float, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using Alpha = nb::ndarray<const float, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using MutableAlpha = nb::ndarray<float, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using Coeff4 = nb::ndarray<float, nb::numpy, nb::shape<-1, -1, 4>, nb::c_contig>;
using IndexMap = nb::ndarray<const std::int32_t, nb::numpy, nb::shape<-1>, nb::c_contig>;

struct PixelSolutionInputs {
  float alpha;
  float image_r;
  float image_g;
  float image_b;
  float foreground_weighted_sum_r;
  float foreground_weighted_sum_g;
  float foreground_weighted_sum_b;
  float background_weighted_sum_r;
  float background_weighted_sum_g;
  float background_weighted_sum_b;
  float inverse_weight_sum;
  float inverse_weight_sum_plus_one;
  float foreground_gain;
  float background_gain;
};

struct NeighborOffset {
  int dy;
  int dx;
};

enum class AlphaRegion : int {
  low = 0,
  middle = 1,
  high = 2,
};

enum class SweepColor : int {
  red = 0,
  black = 1,
};

template <std::size_t N>
consteval std::array<int, N> make_dense_indices() {
  std::array<int, N> indices {};
  for (std::size_t i = 0; i < N; ++i) {
    indices[i] = static_cast<int>(i);
  }
  return indices;
}

consteval std::array<NeighborOffset, 4> make_neighbor_offsets() {
  return {{{0, -1}, {0, 1}, {-1, 0}, {1, 0}}};
}

inline constexpr int kChannels = 3;
inline constexpr int kNeighborCount = 4;
inline constexpr float kAlphaLowThreshold = 0.01f;
inline constexpr float kAlphaHighThreshold = 0.99f;
inline constexpr float kInitialForegroundThreshold = 0.9f;
inline constexpr float kInitialBackgroundThreshold = 0.1f;
inline constexpr auto kChannelIndices = make_dense_indices<kChannels>();
inline constexpr auto kNeighborIndices = make_dense_indices<kNeighborCount>();
inline constexpr auto kNeighborOffsets = make_neighbor_offsets();

template <typename T>
inline constexpr T clamp01(T value) {
  return std::clamp(value, static_cast<T>(0), static_cast<T>(1));
}

inline constexpr int clamp_index(int value, int upper_bound) {
  return std::clamp(value, 0, upper_bound);
}

inline constexpr AlphaRegion classify_alpha_region(float alpha) {
  if (alpha < kAlphaLowThreshold) {
    return AlphaRegion::low;
  }
  if (alpha > kAlphaHighThreshold) {
    return AlphaRegion::high;
  }
  return AlphaRegion::middle;
}

inline constexpr int parity_of(int y, SweepColor color) {
  return (static_cast<int>(color) + y) & 1;
}

inline constexpr int interior_x_start(int y, SweepColor color) {
  return parity_of(y, color) == 0 ? 2 : 1;
}

inline constexpr int ceil_log2_int(int value) {
  if (value <= 1) {
    return 0;
  }
  int result = 0;
  int current = 1;
  while (current < value) {
    current <<= 1;
    ++result;
  }
  return result;
}

inline constexpr std::size_t scalar_index(std::size_t y, std::size_t x, std::size_t w) {
  return y * w + x;
}

inline constexpr std::size_t rgb_index(std::size_t y, std::size_t x, std::size_t w) {
  return (y * w + x) * kChannels;
}

inline constexpr std::size_t rgb_pixel_base(std::size_t idx) {
  return idx * kChannels;
}

template <typename Fn, std::size_t... Cs>
inline constexpr void apply_rgb_impl(Fn &&fn, std::index_sequence<Cs...>) {
  (fn(std::integral_constant<std::size_t, Cs> {}), ...);
}

template <typename Fn>
inline constexpr void apply_rgb(Fn &&fn) {
  apply_rgb_impl(std::forward<Fn>(fn), std::make_index_sequence<kChannels> {});
}

template <typename T>
struct BufferScalarView {
  T *data;
  int width;

  decltype(auto) operator()(int y, int x) const { return data[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(width))]; }
};

template <typename T, std::size_t Channels>
struct BufferTensorView {
  T *data;
  int width;

  decltype(auto) operator()(int y, int x, std::size_t c) const {
    return data[(scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(width)) * Channels) + c];
  }

  T *pixel(std::size_t idx) const { return data + idx * Channels; }
};

using ConstScalarView = BufferScalarView<const float>;
using MutableScalarView = BufferScalarView<float>;
using ConstRgbView = BufferTensorView<const float, kChannels>;
using MutableRgbView = BufferTensorView<float, kChannels>;
using MutableCoeffView = BufferTensorView<float, kNeighborCount>;

inline void validate_float_outputs(MutableImage foreground_output, MutableImage background_output, int h0, int w0) {
  if (static_cast<int>(foreground_output.shape(0)) != h0 || static_cast<int>(foreground_output.shape(1)) != w0 ||
      static_cast<int>(foreground_output.shape(2)) != kChannels || static_cast<int>(background_output.shape(0)) != h0 ||
      static_cast<int>(background_output.shape(1)) != w0 || static_cast<int>(background_output.shape(2)) != kChannels) {
    throw std::runtime_error("estimate_multilevel_foreground_background: output shapes must match the input image");
  }
}
