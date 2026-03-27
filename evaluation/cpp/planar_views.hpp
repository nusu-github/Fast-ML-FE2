#pragma once

#include "common.hpp"

#include <array>
#include <span>

template <typename T>
struct PlaneView {
  T *data;
  int stride;

  decltype(auto) operator()(int y, int x) const {
    return data[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(stride))];
  }

  T *row(int y) const { return data + static_cast<std::size_t>(y) * static_cast<std::size_t>(stride); }
  std::span<T> row_span(int y) const { return {row(y), static_cast<std::size_t>(stride)}; }
};

using ConstPlaneView = PlaneView<const float>;
using MutablePlaneView = PlaneView<float>;

template <typename T>
struct PlanarRgbView {
  std::array<T *, kChannels> channels;
  int stride;

  decltype(auto) operator()(int y, int x, std::size_t c) const {
    return channels[c][scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(stride))];
  }

  T *channel(std::size_t c) const { return channels[c]; }
  T *row(std::size_t c, int y) const { return channels[c] + static_cast<std::size_t>(y) * static_cast<std::size_t>(stride); }
  std::span<T> row_span(std::size_t c, int y) const { return {row(c, y), static_cast<std::size_t>(stride)}; }
  std::span<T> channel_span(std::size_t c, std::size_t size) const { return {channels[c], size}; }
};

using ConstPlanarRgbView = PlanarRgbView<const float>;
using MutablePlanarRgbView = PlanarRgbView<float>;

struct PlanarCoeffView {
  std::array<float *, kNeighborCount> neighbor_weights;
  float *alpha;
  float *inverse_weight_sum;
  float *inverse_weight_sum_plus_one;
  float *foreground_gain;
  float *background_gain;
  int stride;

  float &neighbor(int y, int x, std::size_t n) const {
    return neighbor_weights[n][scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(stride))];
  }

  float *neighbor_row(std::size_t n, int y) const {
    return neighbor_weights[n] + static_cast<std::size_t>(y) * static_cast<std::size_t>(stride);
  }

  std::span<float> neighbor_row_span(std::size_t n, int y) const {
    return {neighbor_row(n, y), static_cast<std::size_t>(stride)};
  }
};

struct ConstPlanarCoeffView {
  std::array<const float *, kNeighborCount> neighbor_weights;
  const float *alpha;
  const float *inverse_weight_sum;
  const float *inverse_weight_sum_plus_one;
  const float *foreground_gain;
  const float *background_gain;
  int stride;

  float neighbor(int y, int x, std::size_t n) const {
    return neighbor_weights[n][scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(stride))];
  }

  const float *neighbor_row(std::size_t n, int y) const {
    return neighbor_weights[n] + static_cast<std::size_t>(y) * static_cast<std::size_t>(stride);
  }

  std::span<const float> neighbor_row_span(std::size_t n, int y) const {
    return {neighbor_row(n, y), static_cast<std::size_t>(stride)};
  }
};
