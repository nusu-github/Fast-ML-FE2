#pragma once

#include <nanobind/nanobind.h>
#include <nanobind/ndarray.h>

#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <limits>
#include <span>
#include <stdexcept>
#include <vector>

namespace nb = nanobind;

using Image = nb::ndarray<const float, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using MutableImage = nb::ndarray<float, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using Alpha = nb::ndarray<const float, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using MutableAlpha = nb::ndarray<float, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using Coeff4 = nb::ndarray<float, nb::numpy, nb::shape<-1, -1, 4>, nb::c_contig>;
using IndexMap = nb::ndarray<const std::int32_t, nb::numpy, nb::shape<-1>, nb::c_contig>;
using ImageU8 = nb::ndarray<const std::uint8_t, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using MutableImageU8 = nb::ndarray<std::uint8_t, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using AlphaU8 = nb::ndarray<const std::uint8_t, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using MutableAlphaU8 = nb::ndarray<std::uint8_t, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;

struct PixelSolutionInputs {
  float alpha;
  float image0;
  float image1;
  float image2;
  float sum_wF0;
  float sum_wF1;
  float sum_wF2;
  float sum_wB0;
  float sum_wB1;
  float sum_wB2;
  float inv_W;
  float inv_Wp1;
  float fg_gain;
  float bg_gain;
};

struct ResizeIndexMap {
  explicit ResizeIndexMap(int dst_size) : indices(static_cast<std::size_t>(dst_size)) {}
  ResizeIndexMap() = default;

  std::span<int> mutable_span() { return indices; }
  std::span<const int> span() const { return indices; }
  int *data() { return indices.data(); }
  const int *data() const { return indices.data(); }
  void resize(int dst_size) { indices.resize(static_cast<std::size_t>(dst_size)); }

private:
  std::vector<int> indices;
};

struct FloatWorkspace {
  std::vector<float> prevF_storage;
  std::vector<float> prevB_storage;
  std::vector<float> currF_storage;
  std::vector<float> currB_storage;
  std::vector<float> image;
  std::vector<float> alpha;
  std::vector<float> neighbor_weights;
  std::vector<float> inv_W;
  std::vector<float> inv_Wp1;
  std::vector<float> fg_gain;
  std::vector<float> bg_gain;

  void ensure_capacity(std::size_t max_pixels) {
    prevF_storage.resize(max_pixels * 3);
    prevB_storage.resize(max_pixels * 3);
    currF_storage.resize(max_pixels * 3);
    currB_storage.resize(max_pixels * 3);
    image.resize(max_pixels * 3);
    alpha.resize(max_pixels);
    neighbor_weights.resize(max_pixels * 4);
    inv_W.resize(max_pixels);
    inv_Wp1.resize(max_pixels);
    fg_gain.resize(max_pixels);
    bg_gain.resize(max_pixels);
  }
};

struct U8Workspace {
  std::vector<std::uint8_t> prevF_storage;
  std::vector<std::uint8_t> prevB_storage;
  std::vector<std::uint8_t> currF_storage;
  std::vector<std::uint8_t> currB_storage;
  std::vector<std::uint8_t> image;
  std::vector<std::uint8_t> alpha;
  std::vector<float> neighbor_weights;
  std::vector<float> inv_W;
  std::vector<float> inv_Wp1;
  std::vector<float> fg_gain;
  std::vector<float> bg_gain;
  std::vector<std::uint32_t> weight_lut;
  std::array<float, 256> u8_to_f32 {};
  ResizeIndexMap x_map;
  ResizeIndexMap y_map;
  ResizeIndexMap prev_x_map;
  ResizeIndexMap prev_y_map;
  std::uint32_t lut_regularization_bits = 0;
  std::uint32_t lut_gradient_weight_bits = 0;
  bool lut_initialized = false;

  U8Workspace() : weight_lut(256u * 256u) {
    constexpr float inv255 = 1.0f / 255.0f;
    for (int i = 0; i < 256; ++i) {
      u8_to_f32[static_cast<std::size_t>(i)] = static_cast<float>(i) * inv255;
    }
  }

  void ensure_capacity(std::size_t max_pixels) {
    prevF_storage.resize(max_pixels * 3);
    prevB_storage.resize(max_pixels * 3);
    currF_storage.resize(max_pixels * 3);
    currB_storage.resize(max_pixels * 3);
    image.resize(max_pixels * 3);
    alpha.resize(max_pixels);
    neighbor_weights.resize(max_pixels * 4);
    inv_W.resize(max_pixels);
    inv_Wp1.resize(max_pixels);
    fg_gain.resize(max_pixels);
    bg_gain.resize(max_pixels);
  }

  bool needs_weight_lut_refresh(float regularization, float gradient_weight) const {
    return !lut_initialized || lut_regularization_bits != std::bit_cast<std::uint32_t>(regularization) ||
        lut_gradient_weight_bits != std::bit_cast<std::uint32_t>(gradient_weight);
  }

  void mark_weight_lut_ready(float regularization, float gradient_weight) {
    lut_initialized = true;
    lut_regularization_bits = std::bit_cast<std::uint32_t>(regularization);
    lut_gradient_weight_bits = std::bit_cast<std::uint32_t>(gradient_weight);
  }
};

inline float clamp01(float value) {
  return std::clamp(value, 0.0f, 1.0f);
}

inline std::uint8_t quantize01_to_u8(float value) {
  const int quantized = std::clamp(static_cast<int>(value * 255.0f + 0.5f), 0, 255);
  return static_cast<std::uint8_t>(quantized);
}

inline std::uint32_t div255_fast(std::uint32_t x) {
  return (x + ((x + 257u) >> 8)) >> 8;
}

inline std::size_t scalar_index(std::size_t y, std::size_t x, std::size_t w) {
  return y * w + x;
}

inline std::size_t rgb_index(std::size_t y, std::size_t x, std::size_t w) {
  return (y * w + x) * 3;
}

inline void validate_float_outputs(MutableImage foreground, MutableImage background, int h0, int w0) {
  if (static_cast<int>(foreground.shape(0)) != h0 || static_cast<int>(foreground.shape(1)) != w0 ||
      static_cast<int>(foreground.shape(2)) != 3 || static_cast<int>(background.shape(0)) != h0 ||
      static_cast<int>(background.shape(1)) != w0 || static_cast<int>(background.shape(2)) != 3) {
    throw std::runtime_error("estimate_fb_ml: output shapes must match the input image");
  }
}

inline void validate_u8_outputs(MutableImageU8 foreground, MutableImageU8 background, int h0, int w0) {
  if (static_cast<int>(foreground.shape(0)) != h0 || static_cast<int>(foreground.shape(1)) != w0 ||
      static_cast<int>(foreground.shape(2)) != 3 || static_cast<int>(background.shape(0)) != h0 ||
      static_cast<int>(background.shape(1)) != w0 || static_cast<int>(background.shape(2)) != 3) {
    throw std::runtime_error("estimate_fb_ml_u8: output shapes must match the input image");
  }
}
