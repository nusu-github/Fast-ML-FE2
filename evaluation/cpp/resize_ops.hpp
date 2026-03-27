#pragma once

#include "common.hpp"

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
