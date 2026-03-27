#pragma once

#include "planar_views.hpp"

#include <cstdint>
#include <memory>

template <typename T, std::size_t Alignment>
struct AlignedAllocator {
  using value_type = T;

  AlignedAllocator() noexcept = default;

  template <typename U>
  constexpr AlignedAllocator(const AlignedAllocator<U, Alignment> &) noexcept {}

  [[nodiscard]] T *allocate(std::size_t n) {
    if (n > static_cast<std::size_t>(-1) / sizeof(T)) {
      throw std::bad_array_new_length();
    }
    auto *ptr = ::operator new[](n * sizeof(T), std::align_val_t {Alignment});
    return static_cast<T *>(ptr);
  }

  void deallocate(T *ptr, std::size_t) noexcept { ::operator delete[](ptr, std::align_val_t {Alignment}); }

  template <typename U>
  struct rebind {
    using other = AlignedAllocator<U, Alignment>;
  };
};

template <typename T, typename U, std::size_t Alignment>
inline constexpr bool operator==(const AlignedAllocator<T, Alignment> &, const AlignedAllocator<U, Alignment> &) noexcept {
  return true;
}

template <typename T, typename U, std::size_t Alignment>
inline constexpr bool operator!=(const AlignedAllocator<T, Alignment> &, const AlignedAllocator<U, Alignment> &) noexcept {
  return false;
}

using AlignedFloatVector = std::vector<float, AlignedAllocator<float, 64>>;

inline int padded_stride(int width) {
  constexpr int kAlignmentFloats = 16;
  return ((width + kAlignmentFloats - 1) / kAlignmentFloats) * kAlignmentFloats;
}

struct PlanarRgbStorage {
  std::array<AlignedFloatVector, kChannels> channels;

  void resize(std::size_t size) {
    for (auto &channel : channels) {
      channel.resize(size);
    }
  }

  MutablePlanarRgbView mutable_view(int stride) {
    return MutablePlanarRgbView {
        .channels = {channels[0].data(), channels[1].data(), channels[2].data()},
        .stride = stride,
    };
  }

  ConstPlanarRgbView const_view(int stride) const {
    return ConstPlanarRgbView {
        .channels = {channels[0].data(), channels[1].data(), channels[2].data()},
        .stride = stride,
    };
  }
};

struct PlanarCoeffStorage {
  std::array<AlignedFloatVector, kNeighborCount> neighbor_weights;
  AlignedFloatVector alpha;
  AlignedFloatVector inverse_weight_sum;
  AlignedFloatVector inverse_weight_sum_plus_one;
  AlignedFloatVector foreground_gain;
  AlignedFloatVector background_gain;

  void resize(std::size_t size) {
    for (auto &weights : neighbor_weights) {
      weights.resize(size);
    }
    alpha.resize(size);
    inverse_weight_sum.resize(size);
    inverse_weight_sum_plus_one.resize(size);
    foreground_gain.resize(size);
    background_gain.resize(size);
  }

  PlanarCoeffView mutable_view(int stride) {
    return PlanarCoeffView {
        .neighbor_weights = {
            neighbor_weights[0].data(),
            neighbor_weights[1].data(),
            neighbor_weights[2].data(),
            neighbor_weights[3].data(),
        },
        .alpha = alpha.data(),
        .inverse_weight_sum = inverse_weight_sum.data(),
        .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one.data(),
        .foreground_gain = foreground_gain.data(),
        .background_gain = background_gain.data(),
        .stride = stride,
    };
  }

  ConstPlanarCoeffView const_view(int stride) const {
    return ConstPlanarCoeffView {
        .neighbor_weights = {
            neighbor_weights[0].data(),
            neighbor_weights[1].data(),
            neighbor_weights[2].data(),
            neighbor_weights[3].data(),
        },
        .alpha = alpha.data(),
        .inverse_weight_sum = inverse_weight_sum.data(),
        .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one.data(),
        .foreground_gain = foreground_gain.data(),
        .background_gain = background_gain.data(),
        .stride = stride,
    };
  }
};

struct FloatWorkspace {
  int max_height = 0;
  int max_width = 0;
  int stride = 0;

  PlanarRgbStorage previous_foreground;
  PlanarRgbStorage previous_background;
  PlanarRgbStorage current_foreground;
  PlanarRgbStorage current_background;
  PlanarCoeffStorage coeffs;
  std::vector<std::int32_t> x_index_map;
  std::vector<std::int32_t> y_index_map;

  void ensure_capacity(int max_h, int max_w) {
    max_height = max_h;
    max_width = max_w;
    stride = padded_stride(max_w);
    const std::size_t plane_size = static_cast<std::size_t>(stride) * static_cast<std::size_t>(max_h);

    previous_foreground.resize(plane_size);
    previous_background.resize(plane_size);
    current_foreground.resize(plane_size);
    current_background.resize(plane_size);
    coeffs.resize(plane_size);
    x_index_map.resize(static_cast<std::size_t>(max_w));
    y_index_map.resize(static_cast<std::size_t>(max_h));
  }
};

constinit inline thread_local FloatWorkspace *g_thread_workspace = nullptr;

inline FloatWorkspace &thread_workspace() {
  thread_local FloatWorkspace workspace_storage;
  if (g_thread_workspace == nullptr) {
    g_thread_workspace = &workspace_storage;
  }
  return *g_thread_workspace;
}
