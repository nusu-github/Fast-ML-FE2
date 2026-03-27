#pragma once

#include "common.hpp"

#include <vector>

inline void build_resize_index_map_buffer(int src_size, int dst_size, std::int32_t *dst) {
  for (int i_dst = 0; i_dst < dst_size; ++i_dst) {
    dst[i_dst] = static_cast<std::int32_t>(std::min(src_size - 1, i_dst * src_size / dst_size));
  }
}

inline void resize_nearest_rgb_buffer(
    float *dst,
    const float *src,
    int h_src,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
    const float *src_row = src + static_cast<std::size_t>(y_src) * static_cast<std::size_t>(w_src) * kChannels;
    float *dst_row = dst + static_cast<std::size_t>(y_dst) * static_cast<std::size_t>(w_dst) * kChannels;
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
      const float *src_px = src_row + static_cast<std::size_t>(x_src) * kChannels;
      float *dst_px = dst_row + static_cast<std::size_t>(x_dst) * kChannels;
      apply_rgb([&]<std::size_t C>(std::integral_constant<std::size_t, C>) {
        dst_px[C] = src_px[C];
      });
    }
  }
}

inline void resize_nearest_scalar_buffer(float *dst, const float *src, int h_src, int w_src, int h_dst, int w_dst) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
    const float *src_row = src + static_cast<std::size_t>(y_src) * static_cast<std::size_t>(w_src);
    float *dst_row = dst + static_cast<std::size_t>(y_dst) * static_cast<std::size_t>(w_dst);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
      dst_row[x_dst] = src_row[x_src];
    }
  }
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

inline auto build_resize_index_map(int src_size, int dst_size) -> std::vector<std::int32_t> {
  std::vector<std::int32_t> result(static_cast<std::size_t>(dst_size));
  build_resize_index_map_buffer(src_size, dst_size, result.data());
  return result;
}
