#pragma once

#include "common.hpp"
#include "resize_ops.hpp"

namespace {

constexpr std::uint32_t kFxWeightScale = 1u << 16;
constexpr std::uint32_t kFxRecipFracBits = 24;
constexpr std::uint64_t kFxRecipScale = 1ull << kFxRecipFracBits;
constexpr std::uint64_t kFxCodeRecipNumerator = 1ull << 40;
constexpr std::uint32_t kAlphaCodeScale = 255u;
constexpr std::uint32_t kAlphaSquareDenom = kAlphaCodeScale * kAlphaCodeScale;
constexpr std::uint32_t kFxStateFracBits = 8u;
constexpr std::uint32_t kFxStateScale = 1u << kFxStateFracBits;
constexpr std::uint32_t kFxStateMax = kAlphaCodeScale * kFxStateScale;
constexpr std::uint8_t kAlphaLowThreshold = 2;
constexpr std::uint8_t kAlphaHighThreshold = 253;

struct FxU8Workspace {
  std::vector<std::uint16_t> previous_foreground_storage;
  std::vector<std::uint16_t> previous_background_storage;
  std::vector<std::uint16_t> current_foreground_storage;
  std::vector<std::uint16_t> current_background_storage;
  std::vector<std::uint8_t> image;
  std::vector<std::uint8_t> alpha;
  std::vector<std::uint16_t> neighbor_weights;
  std::vector<std::uint32_t> inverse_weight_sum;
  std::vector<std::uint32_t> inverse_weight_sum_plus_one;
  std::vector<std::uint32_t> foreground_gain;
  std::vector<std::uint32_t> background_gain;
  std::vector<std::uint16_t> weight_lut;
  ResizeIndexMap x_index_map;
  ResizeIndexMap y_index_map;
  ResizeIndexMap previous_x_index_map;
  ResizeIndexMap previous_y_index_map;
  std::uint16_t lut_regularization_q16 = 0;
  std::uint16_t lut_gradient_step_q16 = 0;
  bool lut_initialized = false;

  FxU8Workspace() : weight_lut(256u * 256u) {}

  void ensure_capacity(std::size_t max_pixels) {
    previous_foreground_storage.resize(max_pixels * 3);
    previous_background_storage.resize(max_pixels * 3);
    current_foreground_storage.resize(max_pixels * 3);
    current_background_storage.resize(max_pixels * 3);
    image.resize(max_pixels * 3);
    alpha.resize(max_pixels);
    neighbor_weights.resize(max_pixels * 4);
    inverse_weight_sum.resize(max_pixels);
    inverse_weight_sum_plus_one.resize(max_pixels);
    foreground_gain.resize(max_pixels);
    background_gain.resize(max_pixels);
  }

  bool needs_weight_lut_refresh(std::uint16_t regularization_q16, std::uint16_t gradient_step_q16) const {
    return !lut_initialized || lut_regularization_q16 != regularization_q16 ||
        lut_gradient_step_q16 != gradient_step_q16;
  }

  void mark_weight_lut_ready(std::uint16_t regularization_q16, std::uint16_t gradient_step_q16) {
    lut_initialized = true;
    lut_regularization_q16 = regularization_q16;
    lut_gradient_step_q16 = gradient_step_q16;
  }
};

inline std::uint8_t clamp_u8_from_int(int value) {
  return static_cast<std::uint8_t>(std::clamp(value, 0, 255));
}

inline std::uint16_t clamp_state_from_int(int value) {
  return static_cast<std::uint16_t>(std::clamp(value, 0, static_cast<int>(kFxStateMax)));
}

inline std::uint8_t quantize_state_to_u8(std::uint16_t state_code) {
  return clamp_u8_from_int((static_cast<int>(state_code) + static_cast<int>(kFxStateScale / 2u)) >>
                           kFxStateFracBits);
}

inline std::uint16_t quantize_q16_checked(double value, const char *name) {
  if (!std::isfinite(value)) {
    throw std::runtime_error(std::string("estimate_multilevel_foreground_background_fx_u8: ") + name +
                             " must be finite");
  }
  const long long quantized = std::llround(value * static_cast<double>(kFxWeightScale));
  if (quantized <= 0 || quantized > static_cast<long long>(std::numeric_limits<std::uint16_t>::max())) {
    throw std::runtime_error(std::string("estimate_multilevel_foreground_background_fx_u8: ") + name +
                             " exceeds fixed-point safe range");
  }
  return static_cast<std::uint16_t>(quantized);
}

inline std::uint16_t quantize_gradient_step_q16_checked(double gradient_weight) {
  if (!std::isfinite(gradient_weight)) {
    throw std::runtime_error("estimate_multilevel_foreground_background_fx_u8: gradient_weight must be finite");
  }
  const long long quantized =
      std::llround(gradient_weight * static_cast<double>(kFxWeightScale) / static_cast<double>(kAlphaCodeScale));
  if (quantized < 0 || quantized > static_cast<long long>(std::numeric_limits<std::uint16_t>::max())) {
    throw std::runtime_error("estimate_multilevel_foreground_background_fx_u8: gradient_weight exceeds fixed-point "
                             "safe range");
  }
  return static_cast<std::uint16_t>(quantized);
}

inline std::uint32_t div_round_u64_to_u32(std::uint64_t numerator, std::uint64_t denominator) {
  return static_cast<std::uint32_t>((numerator + denominator / 2u) / denominator);
}

inline std::int64_t mul_q24_round_signed_i64(std::int64_t value, std::uint32_t coeff_q24) {
  const std::int64_t product = value * static_cast<std::int64_t>(coeff_q24);
  const std::int64_t bias = static_cast<std::int64_t>(1) << (kFxRecipFracBits - 1);
  if (product >= 0) {
    return (product + bias) >> kFxRecipFracBits;
  }
  return -(((-product) + bias) >> kFxRecipFracBits);
}

inline int round_q24_to_int(std::int64_t value_q24) {
  const std::int64_t bias = static_cast<std::int64_t>(1) << (kFxRecipFracBits - 1);
  if (value_q24 >= 0) {
    return static_cast<int>((value_q24 + bias) >> kFxRecipFracBits);
  }
  return -static_cast<int>(((-value_q24) + bias) >> kFxRecipFracBits);
}

inline void compute_initial_means_fx_u8_buffer(
    const std::uint8_t *image,
    const std::uint8_t *alpha,
    int h,
    int w,
    std::uint8_t fg_mean[3],
    std::uint8_t bg_mean[3]
) {
  std::uint64_t fg_sum[3] {0, 0, 0};
  std::uint64_t bg_sum[3] {0, 0, 0};
  std::uint32_t fg_count = 0;
  std::uint32_t bg_count = 0;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      const std::uint8_t a0 = alpha[idx];
      const std::uint8_t *px = image + idx * 3;
      if (a0 >= 230) {
        fg_sum[0] += px[0];
        fg_sum[1] += px[1];
        fg_sum[2] += px[2];
        ++fg_count;
      }
      if (a0 <= 25) {
        bg_sum[0] += px[0];
        bg_sum[1] += px[1];
        bg_sum[2] += px[2];
        ++bg_count;
      }
    }
  }

  for (int c = 0; c < 3; ++c) {
    fg_mean[c] = fg_count > 0 ? clamp_u8_from_int(static_cast<int>((fg_sum[c] + fg_count / 2u) / fg_count))
                              : static_cast<std::uint8_t>(0);
    bg_mean[c] = bg_count > 0 ? clamp_u8_from_int(static_cast<int>((bg_sum[c] + bg_count / 2u) / bg_count))
                              : static_cast<std::uint8_t>(0);
  }
}

inline void build_weight_lut_fx_u8_buffer(
    FxU8Workspace &workspace,
    std::uint16_t regularization_q16,
    std::uint16_t gradient_step_q16
) {
  for (int a0 = 0; a0 < 256; ++a0) {
    for (int a1 = 0; a1 < 256; ++a1) {
      const std::uint32_t diff = static_cast<std::uint32_t>(std::abs(a0 - a1));
      const std::uint32_t weight =
          static_cast<std::uint32_t>(regularization_q16) + static_cast<std::uint32_t>(gradient_step_q16) * diff;
      if (weight == 0 || weight > std::numeric_limits<std::uint16_t>::max()) {
        throw std::runtime_error(
            "estimate_multilevel_foreground_background_fx_u8: fixed-point parameters exceed weight safe range");
      }
      workspace.weight_lut[static_cast<std::size_t>(a0) * 256u + static_cast<std::size_t>(a1)] =
          static_cast<std::uint16_t>(weight);
    }
  }
  workspace.mark_weight_lut_ready(regularization_q16, gradient_step_q16);
}

inline void resize_nearest_rgb_u16_buffer(
    std::uint16_t *dst,
    const std::uint16_t *src,
    const int *x_index_map,
    const int *y_index_map,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::uint16_t *src_row = src + static_cast<std::size_t>(y_index_map[y_dst]) * w_src * 3;
    std::uint16_t *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst * 3;
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const std::uint16_t *src_px = src_row + static_cast<std::size_t>(x_index_map[x_dst]) * 3;
      std::uint16_t *dst_px = dst_row + static_cast<std::size_t>(x_dst) * 3;
      dst_px[0] = src_px[0];
      dst_px[1] = src_px[1];
      dst_px[2] = src_px[2];
    }
  }
}

inline void build_level_solver_coefficients_fx_u8_buffer(FxU8Workspace &workspace, int h, int w) {
  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      const std::uint8_t a0 = workspace.alpha[idx];
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;
      const int y_up = y == 0 ? 0 : y - 1;
      const int y_down = y + 1 >= h ? h - 1 : y + 1;

      const std::uint16_t w0 =
          workspace.weight_lut[static_cast<std::size_t>(a0) * 256u + workspace.alpha[scalar_index(
                                                                                static_cast<std::size_t>(y),
                                                                                static_cast<std::size_t>(x_left),
                                                                                static_cast<std::size_t>(w))]];
      const std::uint16_t w1 =
          workspace.weight_lut[static_cast<std::size_t>(a0) * 256u + workspace.alpha[scalar_index(
                                                                                static_cast<std::size_t>(y),
                                                                                static_cast<std::size_t>(x_right),
                                                                                static_cast<std::size_t>(w))]];
      const std::uint16_t w2 =
          workspace.weight_lut[static_cast<std::size_t>(a0) * 256u + workspace.alpha[scalar_index(
                                                                                static_cast<std::size_t>(y_up),
                                                                                static_cast<std::size_t>(x),
                                                                                static_cast<std::size_t>(w))]];
      const std::uint16_t w3 =
          workspace.weight_lut[static_cast<std::size_t>(a0) * 256u + workspace.alpha[scalar_index(
                                                                                static_cast<std::size_t>(y_down),
                                                                                static_cast<std::size_t>(x),
                                                                                static_cast<std::size_t>(w))]];

      workspace.neighbor_weights[idx * 4 + 0] = w0;
      workspace.neighbor_weights[idx * 4 + 1] = w1;
      workspace.neighbor_weights[idx * 4 + 2] = w2;
      workspace.neighbor_weights[idx * 4 + 3] = w3;

      const std::uint32_t W =
          static_cast<std::uint32_t>(w0) + static_cast<std::uint32_t>(w1) + static_cast<std::uint32_t>(w2) +
          static_cast<std::uint32_t>(w3);
      if (W == 0) {
        throw std::runtime_error(
            "estimate_multilevel_foreground_background_fx_u8: zero total weight is unsupported");
      }

      workspace.inverse_weight_sum[idx] = div_round_u64_to_u32(kFxRecipScale, W);
      workspace.inverse_weight_sum_plus_one[idx] =
          div_round_u64_to_u32(kFxCodeRecipNumerator, static_cast<std::uint64_t>(kAlphaCodeScale) * (W + kFxWeightScale));

      const std::uint32_t alpha_comp = kAlphaCodeScale - a0;
      const std::uint32_t alpha_quad =
          static_cast<std::uint32_t>(a0) * static_cast<std::uint32_t>(a0) + alpha_comp * alpha_comp;
      const std::uint64_t gain_denominator =
          static_cast<std::uint64_t>(kAlphaSquareDenom) * W +
          static_cast<std::uint64_t>(kFxWeightScale) * alpha_quad;
      workspace.foreground_gain[idx] =
          div_round_u64_to_u32(static_cast<std::uint64_t>(a0) * kFxCodeRecipNumerator, gain_denominator);
      workspace.background_gain[idx] =
          div_round_u64_to_u32(static_cast<std::uint64_t>(alpha_comp) * kFxCodeRecipNumerator, gain_denominator);
    }
  }
}

inline void update_red_black_half_step_fx_u8_buffer(
    std::uint16_t *foreground,
    std::uint16_t *background,
    const std::uint8_t *image,
    const std::uint8_t *alpha,
    const std::uint16_t *neighbor_weights,
    const std::uint32_t *inverse_weight_sum,
    const std::uint32_t *inverse_weight_sum_plus_one,
    const std::uint32_t *foreground_gain,
    const std::uint32_t *background_gain,
    int h,
    int w,
    int color
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  auto weighted_mean_state_q24 = [](std::uint64_t weighted_sum, std::uint32_t inverse_weight_sum_q24) {
    return static_cast<std::int64_t>(weighted_sum) * static_cast<std::int64_t>(inverse_weight_sum_q24);
  };

  auto process_pixel = [&](int y, int x) {
    const std::size_t idx =
        scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::uint8_t alpha0 = alpha[idx];
    const int x_left = x == 0 ? 0 : x - 1;
    const int x_right = x + 1 >= w ? w - 1 : x + 1;
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = y + 1 >= h ? h - 1 : y + 1;

    const std::size_t idx_left =
        scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w));
    const std::size_t idx_right =
        scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w));
    const std::size_t idx_up =
        scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::size_t idx_down =
        scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w));

    const std::uint32_t w0 = neighbor_weights[idx * 4 + 0];
    const std::uint32_t w1 = neighbor_weights[idx * 4 + 1];
    const std::uint32_t w2 = neighbor_weights[idx * 4 + 2];
    const std::uint32_t w3 = neighbor_weights[idx * 4 + 3];

    const std::uint64_t fg_sum_r = static_cast<std::uint64_t>(w0) * foreground[idx_left * 3 + 0] +
        static_cast<std::uint64_t>(w1) * foreground[idx_right * 3 + 0] +
        static_cast<std::uint64_t>(w2) * foreground[idx_up * 3 + 0] +
        static_cast<std::uint64_t>(w3) * foreground[idx_down * 3 + 0];
    const std::uint64_t fg_sum_g = static_cast<std::uint64_t>(w0) * foreground[idx_left * 3 + 1] +
        static_cast<std::uint64_t>(w1) * foreground[idx_right * 3 + 1] +
        static_cast<std::uint64_t>(w2) * foreground[idx_up * 3 + 1] +
        static_cast<std::uint64_t>(w3) * foreground[idx_down * 3 + 1];
    const std::uint64_t fg_sum_b = static_cast<std::uint64_t>(w0) * foreground[idx_left * 3 + 2] +
        static_cast<std::uint64_t>(w1) * foreground[idx_right * 3 + 2] +
        static_cast<std::uint64_t>(w2) * foreground[idx_up * 3 + 2] +
        static_cast<std::uint64_t>(w3) * foreground[idx_down * 3 + 2];
    const std::uint64_t bg_sum_r = static_cast<std::uint64_t>(w0) * background[idx_left * 3 + 0] +
        static_cast<std::uint64_t>(w1) * background[idx_right * 3 + 0] +
        static_cast<std::uint64_t>(w2) * background[idx_up * 3 + 0] +
        static_cast<std::uint64_t>(w3) * background[idx_down * 3 + 0];
    const std::uint64_t bg_sum_g = static_cast<std::uint64_t>(w0) * background[idx_left * 3 + 1] +
        static_cast<std::uint64_t>(w1) * background[idx_right * 3 + 1] +
        static_cast<std::uint64_t>(w2) * background[idx_up * 3 + 1] +
        static_cast<std::uint64_t>(w3) * background[idx_down * 3 + 1];
    const std::uint64_t bg_sum_b = static_cast<std::uint64_t>(w0) * background[idx_left * 3 + 2] +
        static_cast<std::uint64_t>(w1) * background[idx_right * 3 + 2] +
        static_cast<std::uint64_t>(w2) * background[idx_up * 3 + 2] +
        static_cast<std::uint64_t>(w3) * background[idx_down * 3 + 2];

    const std::int64_t mu_f_r_q24 = weighted_mean_state_q24(fg_sum_r, inverse_weight_sum[idx]);
    const std::int64_t mu_f_g_q24 = weighted_mean_state_q24(fg_sum_g, inverse_weight_sum[idx]);
    const std::int64_t mu_f_b_q24 = weighted_mean_state_q24(fg_sum_b, inverse_weight_sum[idx]);
    const std::int64_t mu_b_r_q24 = weighted_mean_state_q24(bg_sum_r, inverse_weight_sum[idx]);
    const std::int64_t mu_b_g_q24 = weighted_mean_state_q24(bg_sum_g, inverse_weight_sum[idx]);
    const std::int64_t mu_b_b_q24 = weighted_mean_state_q24(bg_sum_b, inverse_weight_sum[idx]);

    const std::size_t image_idx = idx * 3;
    const int alpha_code = static_cast<int>(alpha0);
    const int alpha_comp_code = static_cast<int>(kAlphaCodeScale - alpha0);
    const int image_r = image[image_idx + 0];
    const int image_g = image[image_idx + 1];
    const int image_b = image[image_idx + 2];

    const std::int64_t image_r_q24 = static_cast<std::int64_t>(kAlphaCodeScale) * image_r *
        static_cast<std::int64_t>(kFxStateScale) * static_cast<std::int64_t>(kFxRecipScale);
    const std::int64_t image_g_q24 = static_cast<std::int64_t>(kAlphaCodeScale) * image_g *
        static_cast<std::int64_t>(kFxStateScale) * static_cast<std::int64_t>(kFxRecipScale);
    const std::int64_t image_b_q24 = static_cast<std::int64_t>(kAlphaCodeScale) * image_b *
        static_cast<std::int64_t>(kFxStateScale) * static_cast<std::int64_t>(kFxRecipScale);

    const std::int64_t residual_r_q24 =
        image_r_q24 - static_cast<std::int64_t>(alpha_code) * mu_f_r_q24 -
        static_cast<std::int64_t>(alpha_comp_code) * mu_b_r_q24;
    const std::int64_t residual_g_q24 =
        image_g_q24 - static_cast<std::int64_t>(alpha_code) * mu_f_g_q24 -
        static_cast<std::int64_t>(alpha_comp_code) * mu_b_g_q24;
    const std::int64_t residual_b_q24 =
        image_b_q24 - static_cast<std::int64_t>(alpha_code) * mu_f_b_q24 -
        static_cast<std::int64_t>(alpha_comp_code) * mu_b_b_q24;

    std::uint16_t *foreground_px = foreground + idx * 3;
    std::uint16_t *background_px = background + idx * 3;

    if (alpha0 <= kAlphaLowThreshold) {
      foreground_px[0] = clamp_state_from_int(round_q24_to_int(mu_f_r_q24));
      foreground_px[1] = clamp_state_from_int(round_q24_to_int(mu_f_g_q24));
      foreground_px[2] = clamp_state_from_int(round_q24_to_int(mu_f_b_q24));
      background_px[0] = clamp_state_from_int(
          round_q24_to_int(mu_b_r_q24 + mul_q24_round_signed_i64(residual_r_q24, inverse_weight_sum_plus_one[idx])));
      background_px[1] = clamp_state_from_int(
          round_q24_to_int(mu_b_g_q24 + mul_q24_round_signed_i64(residual_g_q24, inverse_weight_sum_plus_one[idx])));
      background_px[2] = clamp_state_from_int(
          round_q24_to_int(mu_b_b_q24 + mul_q24_round_signed_i64(residual_b_q24, inverse_weight_sum_plus_one[idx])));
      return;
    }

    if (alpha0 >= kAlphaHighThreshold) {
      foreground_px[0] = clamp_state_from_int(
          round_q24_to_int(mu_f_r_q24 + mul_q24_round_signed_i64(residual_r_q24, inverse_weight_sum_plus_one[idx])));
      foreground_px[1] = clamp_state_from_int(
          round_q24_to_int(mu_f_g_q24 + mul_q24_round_signed_i64(residual_g_q24, inverse_weight_sum_plus_one[idx])));
      foreground_px[2] = clamp_state_from_int(
          round_q24_to_int(mu_f_b_q24 + mul_q24_round_signed_i64(residual_b_q24, inverse_weight_sum_plus_one[idx])));
      background_px[0] = clamp_state_from_int(round_q24_to_int(mu_b_r_q24));
      background_px[1] = clamp_state_from_int(round_q24_to_int(mu_b_g_q24));
      background_px[2] = clamp_state_from_int(round_q24_to_int(mu_b_b_q24));
      return;
    }

    foreground_px[0] =
        clamp_state_from_int(round_q24_to_int(mu_f_r_q24 + mul_q24_round_signed_i64(residual_r_q24, foreground_gain[idx])));
    foreground_px[1] =
        clamp_state_from_int(round_q24_to_int(mu_f_g_q24 + mul_q24_round_signed_i64(residual_g_q24, foreground_gain[idx])));
    foreground_px[2] =
        clamp_state_from_int(round_q24_to_int(mu_f_b_q24 + mul_q24_round_signed_i64(residual_b_q24, foreground_gain[idx])));
    background_px[0] =
        clamp_state_from_int(round_q24_to_int(mu_b_r_q24 + mul_q24_round_signed_i64(residual_r_q24, background_gain[idx])));
    background_px[1] =
        clamp_state_from_int(round_q24_to_int(mu_b_g_q24 + mul_q24_round_signed_i64(residual_g_q24, background_gain[idx])));
    background_px[2] =
        clamp_state_from_int(round_q24_to_int(mu_b_b_q24 + mul_q24_round_signed_i64(residual_b_q24, background_gain[idx])));
  };

  if (h > 2 && w > 2) {
    for (int y = 1; y < h - 1; ++y) {
      int x_start = (color + y) % 2;
      x_start = x_start == 0 ? 2 : 1;
      for (int x = x_start; x < w - 1; x += 2) {
        process_pixel(y, x);
      }
    }
  }

  for (int y = 0; y < h; ++y) {
    if (y != 0 && y + 1 < h) {
      continue;
    }
    const int x_start = (color + y) % 2;
    for (int x = x_start; x < w; x += 2) {
      process_pixel(y, x);
    }
  }

  for (int y = 1; y < h - 1; ++y) {
    if (((color + y) % 2) == 0) {
      process_pixel(y, 0);
    }
    if (w > 1 && ((w - 1 + y) % 2) == color) {
      process_pixel(y, w - 1);
    }
  }
}

inline void estimate_multilevel_foreground_background_fx_u8(
    MutableImageU8 foreground_out,
    MutableImageU8 background_out,
    ImageU8 input_image,
    AlphaU8 input_alpha,
    float regularization,
    float gradient_weight,
    int n_small_iterations,
    int n_big_iterations,
    int small_size
) {
  const int h0 = static_cast<int>(input_image.shape(0));
  const int w0 = static_cast<int>(input_image.shape(1));
  validate_u8_outputs(foreground_out, background_out, h0, w0);
  if (h0 <= 0 || w0 <= 0) {
    throw std::runtime_error("estimate_multilevel_foreground_background_fx_u8: input image must be non-empty");
  }

  const std::uint16_t regularization_q16 = quantize_q16_checked(static_cast<double>(regularization), "regularization");
  const std::uint16_t gradient_step_q16 = quantize_gradient_step_q16_checked(static_cast<double>(gradient_weight));
  const std::uint32_t max_weight =
      static_cast<std::uint32_t>(regularization_q16) + static_cast<std::uint32_t>(gradient_step_q16) * 255u;
  if (max_weight == 0 || max_weight > std::numeric_limits<std::uint16_t>::max()) {
    throw std::runtime_error(
        "estimate_multilevel_foreground_background_fx_u8: fixed-point parameters exceed weight safe range");
  }

  const auto *input_image_ptr = input_image.data();
  const auto *input_alpha_ptr = input_alpha.data();

  nb::gil_scoped_release release;

  const std::size_t max_pixels = static_cast<std::size_t>(h0) * static_cast<std::size_t>(w0);
  thread_local FxU8Workspace workspace;
  workspace.ensure_capacity(max_pixels);

  if (workspace.needs_weight_lut_refresh(regularization_q16, gradient_step_q16)) {
    build_weight_lut_fx_u8_buffer(workspace, regularization_q16, gradient_step_q16);
  }

  std::uint8_t fg_mean[3];
  std::uint8_t bg_mean[3];
  compute_initial_means_fx_u8_buffer(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

  workspace.previous_foreground_storage[0] = static_cast<std::uint16_t>(fg_mean[0]) << kFxStateFracBits;
  workspace.previous_foreground_storage[1] = static_cast<std::uint16_t>(fg_mean[1]) << kFxStateFracBits;
  workspace.previous_foreground_storage[2] = static_cast<std::uint16_t>(fg_mean[2]) << kFxStateFracBits;
  workspace.previous_background_storage[0] = static_cast<std::uint16_t>(bg_mean[0]) << kFxStateFracBits;
  workspace.previous_background_storage[1] = static_cast<std::uint16_t>(bg_mean[1]) << kFxStateFracBits;
  workspace.previous_background_storage[2] = static_cast<std::uint16_t>(bg_mean[2]) << kFxStateFracBits;

  int prev_h = 1;
  int prev_w = 1;

  const int max_dim = std::max(h0, w0);
  const int n_levels = (max_dim <= 1) ? 0 : static_cast<int>(std::ceil(std::log2(static_cast<double>(max_dim))));

  for (int i_level = 0; i_level <= n_levels; ++i_level) {
    int w;
    int h;
    int n_iter;

    if (max_dim <= 1) {
      w = 1;
      h = 1;
      n_iter = n_small_iterations;
    } else {
      const double ratio = static_cast<double>(i_level) / static_cast<double>(n_levels);
      w = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(w0), ratio)));
      h = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(h0), ratio)));
      n_iter = (w <= small_size && h <= small_size) ? n_small_iterations : n_big_iterations;
    }

    workspace.x_index_map.resize(w);
    workspace.y_index_map.resize(h);
    build_resize_index_map_buffer(w0, workspace.x_index_map);
    build_resize_index_map_buffer(h0, workspace.y_index_map);
    resize_nearest_rgb_u8_buffer(
        workspace.image.data(),
        input_image_ptr,
        workspace.x_index_map.data(),
        workspace.y_index_map.data(),
        w0,
        h,
        w);
    resize_nearest_scalar_u8_buffer(
        workspace.alpha.data(),
        input_alpha_ptr,
        workspace.x_index_map.data(),
        workspace.y_index_map.data(),
        w0,
        h,
        w);

    build_level_solver_coefficients_fx_u8_buffer(workspace, h, w);

    std::uint16_t *current_foreground = workspace.current_foreground_storage.data();
    std::uint16_t *current_background = workspace.current_background_storage.data();

    workspace.previous_x_index_map.resize(w);
    workspace.previous_y_index_map.resize(h);
    build_resize_index_map_buffer(prev_w, workspace.previous_x_index_map);
    build_resize_index_map_buffer(prev_h, workspace.previous_y_index_map);

    resize_nearest_rgb_u16_buffer(
        current_foreground,
        workspace.previous_foreground_storage.data(),
        workspace.previous_x_index_map.data(),
        workspace.previous_y_index_map.data(),
        prev_w,
        h,
        w);
    resize_nearest_rgb_u16_buffer(
        current_background,
        workspace.previous_background_storage.data(),
        workspace.previous_x_index_map.data(),
        workspace.previous_y_index_map.data(),
        prev_w,
        h,
        w);

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_red_black_half_step_fx_u8_buffer(
          current_foreground,
          current_background,
          workspace.image.data(),
          workspace.alpha.data(),
          workspace.neighbor_weights.data(),
          workspace.inverse_weight_sum.data(),
          workspace.inverse_weight_sum_plus_one.data(),
          workspace.foreground_gain.data(),
          workspace.background_gain.data(),
          h,
          w,
          0);
      update_red_black_half_step_fx_u8_buffer(
          current_foreground,
          current_background,
          workspace.image.data(),
          workspace.alpha.data(),
          workspace.neighbor_weights.data(),
          workspace.inverse_weight_sum.data(),
          workspace.inverse_weight_sum_plus_one.data(),
          workspace.foreground_gain.data(),
          workspace.background_gain.data(),
          h,
          w,
          1);
    }

    if (i_level == n_levels) {
      const std::size_t pixel_count = static_cast<std::size_t>(h) * static_cast<std::size_t>(w);
      for (std::size_t i = 0; i < pixel_count * 3u; ++i) {
        foreground_out.data()[i] = quantize_state_to_u8(current_foreground[i]);
        background_out.data()[i] = quantize_state_to_u8(current_background[i]);
      }
    } else {
      std::swap(workspace.previous_foreground_storage, workspace.current_foreground_storage);
      std::swap(workspace.previous_background_storage, workspace.current_background_storage);
      prev_h = h;
      prev_w = w;
    }
  }
}

}  // namespace
