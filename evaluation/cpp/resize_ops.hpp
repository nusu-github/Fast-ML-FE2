#pragma once

#include "common.hpp"

inline void build_resize_index_map_raw(int src_size, int dst_size, int *index_map) {
  for (int i_dst = 0; i_dst < dst_size; ++i_dst) {
    index_map[i_dst] = std::min(src_size - 1, i_dst * src_size / dst_size);
  }
}

inline void build_resize_index_map_raw(int src_size, ResizeIndexMap &index_map) {
  build_resize_index_map_raw(src_size, static_cast<int>(index_map.mutable_span().size()), index_map.data());
}

inline void resize_nearest_multichannel_raw(
    float *dst,
    const float *src,
    int h_src,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
    const float *src_row = src + static_cast<std::size_t>(y_src) * w_src * 3;
    float *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst * 3;
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
      const float *src_px = src_row + static_cast<std::size_t>(x_src) * 3;
      float *dst_px = dst_row + static_cast<std::size_t>(x_dst) * 3;
      dst_px[0] = src_px[0];
      dst_px[1] = src_px[1];
      dst_px[2] = src_px[2];
    }
  }
}

inline void resize_nearest_raw(float *dst, const float *src, int h_src, int w_src, int h_dst, int w_dst) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const int y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
    const float *src_row = src + static_cast<std::size_t>(y_src) * w_src;
    float *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst;
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const int x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
      dst_row[x_dst] = src_row[x_src];
    }
  }
}

inline void resize_nearest_multichannel_u8_raw(
    std::uint8_t *dst,
    const std::uint8_t *src,
    const int *x_map,
    const int *y_map,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::uint8_t *src_row = src + static_cast<std::size_t>(y_map[y_dst]) * w_src * 3;
    std::uint8_t *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst * 3;
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const std::uint8_t *src_px = src_row + static_cast<std::size_t>(x_map[x_dst]) * 3;
      std::uint8_t *dst_px = dst_row + static_cast<std::size_t>(x_dst) * 3;
      dst_px[0] = src_px[0];
      dst_px[1] = src_px[1];
      dst_px[2] = src_px[2];
    }
  }
}

inline void resize_nearest_u8_raw(
    std::uint8_t *dst,
    const std::uint8_t *src,
    const int *x_map,
    const int *y_map,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::uint8_t *src_row = src + static_cast<std::size_t>(y_map[y_dst]) * w_src;
    std::uint8_t *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst;
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      dst_row[x_dst] = src_row[x_map[x_dst]];
    }
  }
}

inline void resize_nearest_multichannel(MutableImage dst, Image src) {
  const std::size_t h_src = src.shape(0);
  const std::size_t w_src = src.shape(1);
  const std::size_t h_dst = dst.shape(0);
  const std::size_t w_dst = dst.shape(1);

  for (std::size_t y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::size_t y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
    for (std::size_t x_dst = 0; x_dst < w_dst; ++x_dst) {
      const std::size_t x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
      for (std::size_t c = 0; c < 3; ++c) {
        dst(y_dst, x_dst, c) = src(y_src, x_src, c);
      }
    }
  }
}

inline void resize_nearest(MutableAlpha dst, Alpha src) {
  const std::size_t h_src = src.shape(0);
  const std::size_t w_src = src.shape(1);
  const std::size_t h_dst = dst.shape(0);
  const std::size_t w_dst = dst.shape(1);

  for (std::size_t y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::size_t y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
    for (std::size_t x_dst = 0; x_dst < w_dst; ++x_dst) {
      const std::size_t x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
      dst(y_dst, x_dst) = src(y_src, x_src);
    }
  }
}
