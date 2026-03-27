#pragma once

#include "common.hpp"

#include <array>

template <typename T>
struct PlaneView {
  T *data;
  int stride;

  decltype(auto) operator()(int y, int x) const {
    return data[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(stride))];
  }

  T *row(int y) const { return data + static_cast<std::size_t>(y) * static_cast<std::size_t>(stride); }
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
};

using ConstPlanarRgbView = PlanarRgbView<const float>;
using MutablePlanarRgbView = PlanarRgbView<float>;

struct PlanarCoeffView {
  std::array<float *, kNeighborCount> neighbor_weights;
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
};

struct ConstPlanarCoeffView {
  std::array<const float *, kNeighborCount> neighbor_weights;
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
};
