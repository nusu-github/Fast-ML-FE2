#pragma once

#include <nanobind/nanobind.h>
#include <nanobind/ndarray.h>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
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

inline std::size_t scalar_index(std::size_t y, std::size_t x, std::size_t w) {
  return y * w + x;
}

inline std::size_t rgb_index(std::size_t y, std::size_t x, std::size_t w) {
  return (y * w + x) * kChannels;
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
