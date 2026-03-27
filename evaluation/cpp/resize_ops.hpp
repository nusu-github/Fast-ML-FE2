#pragma once

#include "common.hpp"
#include "planar_views.hpp"

#include <span>

inline void build_resize_index_map_buffer(int src_size, int dst_size, std::int32_t *dst) {
  const int src_max = src_size - 1;
  for (int dst_index = 0; dst_index < dst_size; ++dst_index) {
    dst[dst_index] = static_cast<std::int32_t>(clamp_index((dst_index * src_size) / dst_size, src_max));
  }
}

template <typename DstView, typename SrcView, std::size_t Channels>
inline void resize_nearest_buffer(DstView dst, SrcView src, int h_src, int w_src, int h_dst, int w_dst) {
  const int src_h_max = h_src - 1;
  const int src_w_max = w_src - 1;

  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = clamp_index((y_dst * h_src) / h_dst, src_h_max);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = clamp_index((x_dst * w_src) / w_dst, src_w_max);
      if constexpr (Channels == 1) {
        dst(y_dst, x_dst) = src(y_src, x_src);
      } else {
        for (int c : kChannelIndices) {
          dst(y_dst, x_dst, static_cast<std::size_t>(c)) = src(y_src, x_src, static_cast<std::size_t>(c));
        }
      }
    }
  }
}

inline void resize_nearest_rgb_buffer(float *dst, const float *src, int h_src, int w_src, int h_dst, int w_dst) {
  resize_nearest_buffer<MutableRgbView, ConstRgbView, kChannels>(
      MutableRgbView {.data = dst, .width = w_dst},
      ConstRgbView {.data = src, .width = w_src},
      h_src,
      w_src,
      h_dst,
      w_dst);
}

inline void resize_nearest_scalar_buffer(float *dst, const float *src, int h_src, int w_src, int h_dst, int w_dst) {
  resize_nearest_buffer<MutableScalarView, ConstScalarView, 1>(
      MutableScalarView {.data = dst, .width = w_dst},
      ConstScalarView {.data = src, .width = w_src},
      h_src,
      w_src,
      h_dst,
      w_dst);
}

inline void resize_nearest_rgb(MutableImage dst, Image src) {
  resize_nearest_rgb_buffer(
      dst.data(),
      src.data(),
      static_cast<int>(src.shape(0)),
      static_cast<int>(src.shape(1)),
      static_cast<int>(dst.shape(0)),
      static_cast<int>(dst.shape(1)));
}

inline void resize_nearest_scalar(MutableAlpha dst, Alpha src) {
  resize_nearest_scalar_buffer(
      dst.data(),
      src.data(),
      static_cast<int>(src.shape(0)),
      static_cast<int>(src.shape(1)),
      static_cast<int>(dst.shape(0)),
      static_cast<int>(dst.shape(1)));
}

inline void resize_nearest_plane_buffer(
    MutablePlaneView dst,
    ConstPlaneView src,
    int h_src,
    int w_src,
    int h_dst,
    int w_dst
) {
  const int src_h_max = h_src - 1;
  const int src_w_max = w_src - 1;

  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = clamp_index((y_dst * h_src) / h_dst, src_h_max);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = clamp_index((x_dst * w_src) / w_dst, src_w_max);
      dst(y_dst, x_dst) = src(y_src, x_src);
    }
  }
}

inline void resize_nearest_rgb_to_planar(
    MutablePlanarRgbView dst,
    ConstRgbView src,
    int h_src,
    int w_src,
    int h_dst,
    int w_dst
) {
  const int src_h_max = h_src - 1;
  const int src_w_max = w_src - 1;

  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = clamp_index((y_dst * h_src) / h_dst, src_h_max);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = clamp_index((x_dst * w_src) / w_dst, src_w_max);
      for (int c : kChannelIndices) {
        const std::size_t channel = static_cast<std::size_t>(c);
        dst(y_dst, x_dst, channel) = src(y_src, x_src, channel);
      }
    }
  }
}

inline void resize_nearest_planar_rgb(
    MutablePlanarRgbView dst,
    ConstPlanarRgbView src,
    int h_src,
    int w_src,
    int h_dst,
    int w_dst
) {
  const int src_h_max = h_src - 1;
  const int src_w_max = w_src - 1;

  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = clamp_index((y_dst * h_src) / h_dst, src_h_max);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = clamp_index((x_dst * w_src) / w_dst, src_w_max);
      for (int c : kChannelIndices) {
        const std::size_t channel = static_cast<std::size_t>(c);
        dst(y_dst, x_dst, channel) = src(y_src, x_src, channel);
      }
    }
  }
}

inline void export_planar_rgb(
    MutableImage dst,
    ConstPlanarRgbView src,
    int h,
    int w
) {
  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      for (int c : kChannelIndices) {
        const std::size_t channel = static_cast<std::size_t>(c);
        dst(y, x, channel) = src(y, x, channel);
      }
    }
  }
}

inline auto build_resize_index_map(int src_size, int dst_size) -> std::vector<std::int32_t> {
  std::vector<std::int32_t> result(static_cast<std::size_t>(dst_size));
  build_resize_index_map_buffer(src_size, dst_size, result.data());
  return result;
}
