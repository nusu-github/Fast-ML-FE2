#pragma once

#include "common.hpp"
#include "resize_ops.hpp"

namespace {

#if defined(__GNUC__) || defined(__clang__)
#define FX_ALWAYS_INLINE inline __attribute__((always_inline))
#define FX_RESTRICT __restrict__
#else
#define FX_ALWAYS_INLINE inline
#define FX_RESTRICT
#endif

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
constexpr std::uint8_t kBranchLow = 0;
constexpr std::uint8_t kBranchInterior = 1;
constexpr std::uint8_t kBranchHigh = 2;
constexpr std::uint32_t kMaxTotalWeight = 4u * std::numeric_limits<std::uint16_t>::max();
constexpr std::uint64_t kGainSumNumerator = static_cast<std::uint64_t>(kAlphaCodeScale) * kFxCodeRecipNumerator;

inline std::uint32_t div_round_u64_to_u32(std::uint64_t numerator, std::uint64_t denominator);

struct FxCoefficientTables {
  std::vector<std::uint32_t> inverse_weight_sum;
  std::vector<std::uint32_t> inverse_weight_sum_plus_one;
  std::array<std::uint32_t, 256> alpha_quad {};

  FxCoefficientTables()
      : inverse_weight_sum(static_cast<std::size_t>(kMaxTotalWeight) + 1u),
        inverse_weight_sum_plus_one(static_cast<std::size_t>(kMaxTotalWeight) + 1u) {
    inverse_weight_sum[0] = 0;
    inverse_weight_sum_plus_one[0] = 0;
    for (std::uint32_t W = 1; W <= kMaxTotalWeight; ++W) {
      inverse_weight_sum[W] = div_round_u64_to_u32(kFxRecipScale, W);
      inverse_weight_sum_plus_one[W] = div_round_u64_to_u32(
          kFxCodeRecipNumerator,
          static_cast<std::uint64_t>(kAlphaCodeScale) * (static_cast<std::uint64_t>(W) + kFxWeightScale));
    }
    for (std::uint32_t a0 = 0; a0 < 256u; ++a0) {
      const std::uint32_t alpha_comp = kAlphaCodeScale - a0;
      alpha_quad[a0] = a0 * a0 + alpha_comp * alpha_comp;
    }
  }
};

FX_ALWAYS_INLINE const FxCoefficientTables &fx_coefficient_tables() {
  static const FxCoefficientTables tables;
  return tables;
}

struct FxU8Workspace {
  std::array<std::vector<std::uint16_t>, 3> previous_foreground_storage;
  std::array<std::vector<std::uint16_t>, 3> previous_background_storage;
  std::array<std::vector<std::uint16_t>, 3> current_foreground_storage;
  std::array<std::vector<std::uint16_t>, 3> current_background_storage;
  std::array<std::vector<std::uint32_t>, 3> image_term;
  std::vector<std::uint8_t> alpha;
  std::vector<std::uint8_t> branch_mode;
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
    for (int c = 0; c < 3; ++c) {
      previous_foreground_storage[c].resize(max_pixels);
      previous_background_storage[c].resize(max_pixels);
      current_foreground_storage[c].resize(max_pixels);
      current_background_storage[c].resize(max_pixels);
      image_term[c].resize(max_pixels);
    }
    alpha.resize(max_pixels);
    branch_mode.resize(max_pixels);
    neighbor_weights.resize(max_pixels * 4u);
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

FX_ALWAYS_INLINE std::uint8_t clamp_u8_from_int(int value) {
  return static_cast<std::uint8_t>(std::clamp(value, 0, 255));
}

FX_ALWAYS_INLINE std::uint16_t clamp_state_from_int(int value) {
  return static_cast<std::uint16_t>(std::clamp(value, 0, static_cast<int>(kFxStateMax)));
}

FX_ALWAYS_INLINE std::uint8_t quantize_state_to_u8(std::uint16_t state_code) {
  return clamp_u8_from_int(
      (static_cast<int>(state_code) + static_cast<int>(kFxStateScale / 2u)) >> kFxStateFracBits);
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

FX_ALWAYS_INLINE std::uint32_t div_round_u64_to_u32(std::uint64_t numerator, std::uint64_t denominator) {
  return static_cast<std::uint32_t>((numerator + denominator / 2u) / denominator);
}

FX_ALWAYS_INLINE std::uint32_t div_round_u32_by_255(std::uint32_t value) {
  return (value + 127u) / kAlphaCodeScale;
}

FX_ALWAYS_INLINE std::int64_t mul_q24_round_signed_i64(std::int64_t value, std::uint32_t coeff_q24) {
  const std::int64_t product = value * static_cast<std::int64_t>(coeff_q24);
  const std::int64_t bias = static_cast<std::int64_t>(1) << (kFxRecipFracBits - 1);
  return product >= 0 ? ((product + bias) >> kFxRecipFracBits) : -(((-product) + bias) >> kFxRecipFracBits);
}

FX_ALWAYS_INLINE int round_q24_to_int(std::int64_t value_q24) {
  const std::int64_t bias = static_cast<std::int64_t>(1) << (kFxRecipFracBits - 1);
  return value_q24 >= 0 ? static_cast<int>((value_q24 + bias) >> kFxRecipFracBits)
                        : -static_cast<int>(((-value_q24) + bias) >> kFxRecipFracBits);
}

FX_ALWAYS_INLINE std::uint16_t corrected_state_from_q24(
    std::int64_t mean_q24,
    std::int64_t residual_q24,
    std::uint32_t coeff_q24
) {
  return clamp_state_from_int(round_q24_to_int(mean_q24 + mul_q24_round_signed_i64(residual_q24, coeff_q24)));
}

FX_ALWAYS_INLINE std::uint16_t mean_state_from_q24(std::int64_t mean_q24) {
  return clamp_state_from_int(round_q24_to_int(mean_q24));
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
      const std::uint8_t *px = image + idx * 3u;
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

inline void resize_nearest_rgb_u8_to_image_terms(
    std::uint32_t *dst_r,
    std::uint32_t *dst_g,
    std::uint32_t *dst_b,
    const std::uint8_t *src,
    const int *x_index_map,
    const int *y_index_map,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::uint8_t *src_row = src + static_cast<std::size_t>(y_index_map[y_dst]) * w_src * 3u;
    const std::size_t dst_row_offset = static_cast<std::size_t>(y_dst) * static_cast<std::size_t>(w_dst);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      const std::uint8_t *src_px = src_row + static_cast<std::size_t>(x_index_map[x_dst]) * 3u;
      const std::size_t dst_idx = dst_row_offset + static_cast<std::size_t>(x_dst);
      dst_r[dst_idx] = kAlphaCodeScale * static_cast<std::uint32_t>(src_px[0]) * kFxStateScale;
      dst_g[dst_idx] = kAlphaCodeScale * static_cast<std::uint32_t>(src_px[1]) * kFxStateScale;
      dst_b[dst_idx] = kAlphaCodeScale * static_cast<std::uint32_t>(src_px[2]) * kFxStateScale;
    }
  }
}

inline void resize_nearest_planar_u16_buffer(
    std::uint16_t *dst,
    const std::uint16_t *src,
    const int *x_index_map,
    const int *y_index_map,
    int w_src,
    int h_dst,
    int w_dst
) {
  for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
    const std::uint16_t *src_row = src + static_cast<std::size_t>(y_index_map[y_dst]) * static_cast<std::size_t>(w_src);
    std::uint16_t *dst_row = dst + static_cast<std::size_t>(y_dst) * static_cast<std::size_t>(w_dst);
    for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
      dst_row[x_dst] = src_row[x_index_map[x_dst]];
    }
  }
}

inline void build_level_solver_coefficients_fx_u8_buffer(FxU8Workspace &workspace, int h, int w) {
  const FxCoefficientTables &tables = fx_coefficient_tables();
  for (int y = 0; y < h; ++y) {
    const std::size_t row_offset = static_cast<std::size_t>(y) * static_cast<std::size_t>(w);
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = y + 1 >= h ? h - 1 : y + 1;
    for (int x = 0; x < w; ++x) {
      const std::size_t idx = row_offset + static_cast<std::size_t>(x);
      const std::uint8_t a0 = workspace.alpha[idx];
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;

      const std::uint16_t w0 = workspace.weight_lut[static_cast<std::size_t>(a0) * 256u +
          workspace.alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w))]];
      const std::uint16_t w1 = workspace.weight_lut[static_cast<std::size_t>(a0) * 256u +
          workspace.alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w))]];
      const std::uint16_t w2 = workspace.weight_lut[static_cast<std::size_t>(a0) * 256u +
          workspace.alpha[scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]];
      const std::uint16_t w3 = workspace.weight_lut[static_cast<std::size_t>(a0) * 256u +
          workspace.alpha[scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]];

      workspace.neighbor_weights[idx * 4u + 0] = w0;
      workspace.neighbor_weights[idx * 4u + 1] = w1;
      workspace.neighbor_weights[idx * 4u + 2] = w2;
      workspace.neighbor_weights[idx * 4u + 3] = w3;

      const std::uint32_t W =
          static_cast<std::uint32_t>(w0) + static_cast<std::uint32_t>(w1) + static_cast<std::uint32_t>(w2) +
          static_cast<std::uint32_t>(w3);
      if (W == 0) {
        throw std::runtime_error(
            "estimate_multilevel_foreground_background_fx_u8: zero total weight is unsupported");
      }

      workspace.inverse_weight_sum[idx] = tables.inverse_weight_sum[W];
      workspace.inverse_weight_sum_plus_one[idx] = tables.inverse_weight_sum_plus_one[W];

      const std::uint32_t alpha_quad = tables.alpha_quad[a0];
      const std::uint64_t gain_denominator =
          static_cast<std::uint64_t>(kAlphaSquareDenom) * W +
          static_cast<std::uint64_t>(kFxWeightScale) * alpha_quad;
      const std::uint32_t gain_sum = div_round_u64_to_u32(kGainSumNumerator, gain_denominator);
      workspace.foreground_gain[idx] =
          div_round_u32_by_255(static_cast<std::uint32_t>(gain_sum * static_cast<std::uint32_t>(a0)));
      workspace.background_gain[idx] = gain_sum - workspace.foreground_gain[idx];

      workspace.branch_mode[idx] = a0 <= kAlphaLowThreshold ? kBranchLow
                                  : (a0 >= kAlphaHighThreshold ? kBranchHigh : kBranchInterior);
    }
  }
}

FX_ALWAYS_INLINE void update_pixel_fx_u8(
    std::size_t idx,
    std::size_t idx_left,
    std::size_t idx_right,
    std::size_t idx_up,
    std::size_t idx_down,
    std::uint16_t *FX_RESTRICT fg_r,
    std::uint16_t *FX_RESTRICT fg_g,
    std::uint16_t *FX_RESTRICT fg_b,
    std::uint16_t *FX_RESTRICT bg_r,
    std::uint16_t *FX_RESTRICT bg_g,
    std::uint16_t *FX_RESTRICT bg_b,
    const std::uint32_t *FX_RESTRICT image_r,
    const std::uint32_t *FX_RESTRICT image_g,
    const std::uint32_t *FX_RESTRICT image_b,
    const std::uint8_t *FX_RESTRICT alpha,
    const std::uint8_t *FX_RESTRICT branch_mode,
    const std::uint16_t *FX_RESTRICT neighbor_weights,
    const std::uint32_t *FX_RESTRICT inverse_weight_sum,
    const std::uint32_t *FX_RESTRICT inverse_weight_sum_plus_one,
    const std::uint32_t *FX_RESTRICT foreground_gain,
    const std::uint32_t *FX_RESTRICT background_gain
) {
  const std::uint16_t *weights = neighbor_weights + idx * 4u;
  const std::uint32_t w0 = weights[0];
  const std::uint32_t w1 = weights[1];
  const std::uint32_t w2 = weights[2];
  const std::uint32_t w3 = weights[3];

  const std::uint64_t fg_sum_r = static_cast<std::uint64_t>(w0) * fg_r[idx_left] +
      static_cast<std::uint64_t>(w1) * fg_r[idx_right] + static_cast<std::uint64_t>(w2) * fg_r[idx_up] +
      static_cast<std::uint64_t>(w3) * fg_r[idx_down];
  const std::uint64_t fg_sum_g = static_cast<std::uint64_t>(w0) * fg_g[idx_left] +
      static_cast<std::uint64_t>(w1) * fg_g[idx_right] + static_cast<std::uint64_t>(w2) * fg_g[idx_up] +
      static_cast<std::uint64_t>(w3) * fg_g[idx_down];
  const std::uint64_t fg_sum_b = static_cast<std::uint64_t>(w0) * fg_b[idx_left] +
      static_cast<std::uint64_t>(w1) * fg_b[idx_right] + static_cast<std::uint64_t>(w2) * fg_b[idx_up] +
      static_cast<std::uint64_t>(w3) * fg_b[idx_down];
  const std::uint64_t bg_sum_r = static_cast<std::uint64_t>(w0) * bg_r[idx_left] +
      static_cast<std::uint64_t>(w1) * bg_r[idx_right] + static_cast<std::uint64_t>(w2) * bg_r[idx_up] +
      static_cast<std::uint64_t>(w3) * bg_r[idx_down];
  const std::uint64_t bg_sum_g = static_cast<std::uint64_t>(w0) * bg_g[idx_left] +
      static_cast<std::uint64_t>(w1) * bg_g[idx_right] + static_cast<std::uint64_t>(w2) * bg_g[idx_up] +
      static_cast<std::uint64_t>(w3) * bg_g[idx_down];
  const std::uint64_t bg_sum_b = static_cast<std::uint64_t>(w0) * bg_b[idx_left] +
      static_cast<std::uint64_t>(w1) * bg_b[idx_right] + static_cast<std::uint64_t>(w2) * bg_b[idx_up] +
      static_cast<std::uint64_t>(w3) * bg_b[idx_down];

  const std::uint32_t inv_w = inverse_weight_sum[idx];
  const std::int64_t mu_f_r_q24 = static_cast<std::int64_t>(fg_sum_r) * static_cast<std::int64_t>(inv_w);
  const std::int64_t mu_f_g_q24 = static_cast<std::int64_t>(fg_sum_g) * static_cast<std::int64_t>(inv_w);
  const std::int64_t mu_f_b_q24 = static_cast<std::int64_t>(fg_sum_b) * static_cast<std::int64_t>(inv_w);
  const std::int64_t mu_b_r_q24 = static_cast<std::int64_t>(bg_sum_r) * static_cast<std::int64_t>(inv_w);
  const std::int64_t mu_b_g_q24 = static_cast<std::int64_t>(bg_sum_g) * static_cast<std::int64_t>(inv_w);
  const std::int64_t mu_b_b_q24 = static_cast<std::int64_t>(bg_sum_b) * static_cast<std::int64_t>(inv_w);

  const int alpha_code = static_cast<int>(alpha[idx]);
  const int alpha_comp_code = static_cast<int>(kAlphaCodeScale - alpha[idx]);
  const std::int64_t image_r_q24 = static_cast<std::int64_t>(image_r[idx]) << kFxRecipFracBits;
  const std::int64_t image_g_q24 = static_cast<std::int64_t>(image_g[idx]) << kFxRecipFracBits;
  const std::int64_t image_b_q24 = static_cast<std::int64_t>(image_b[idx]) << kFxRecipFracBits;

  const std::int64_t residual_r_q24 =
      image_r_q24 - static_cast<std::int64_t>(alpha_code) * mu_f_r_q24 -
      static_cast<std::int64_t>(alpha_comp_code) * mu_b_r_q24;
  const std::int64_t residual_g_q24 =
      image_g_q24 - static_cast<std::int64_t>(alpha_code) * mu_f_g_q24 -
      static_cast<std::int64_t>(alpha_comp_code) * mu_b_g_q24;
  const std::int64_t residual_b_q24 =
      image_b_q24 - static_cast<std::int64_t>(alpha_code) * mu_f_b_q24 -
      static_cast<std::int64_t>(alpha_comp_code) * mu_b_b_q24;

  if (branch_mode[idx] == kBranchLow) {
    fg_r[idx] = mean_state_from_q24(mu_f_r_q24);
    fg_g[idx] = mean_state_from_q24(mu_f_g_q24);
    fg_b[idx] = mean_state_from_q24(mu_f_b_q24);
    const std::uint32_t coeff = inverse_weight_sum_plus_one[idx];
    bg_r[idx] = corrected_state_from_q24(mu_b_r_q24, residual_r_q24, coeff);
    bg_g[idx] = corrected_state_from_q24(mu_b_g_q24, residual_g_q24, coeff);
    bg_b[idx] = corrected_state_from_q24(mu_b_b_q24, residual_b_q24, coeff);
    return;
  }

  if (branch_mode[idx] == kBranchHigh) {
    const std::uint32_t coeff = inverse_weight_sum_plus_one[idx];
    fg_r[idx] = corrected_state_from_q24(mu_f_r_q24, residual_r_q24, coeff);
    fg_g[idx] = corrected_state_from_q24(mu_f_g_q24, residual_g_q24, coeff);
    fg_b[idx] = corrected_state_from_q24(mu_f_b_q24, residual_b_q24, coeff);
    bg_r[idx] = mean_state_from_q24(mu_b_r_q24);
    bg_g[idx] = mean_state_from_q24(mu_b_g_q24);
    bg_b[idx] = mean_state_from_q24(mu_b_b_q24);
    return;
  }

  const std::uint32_t fg_coeff = foreground_gain[idx];
  const std::uint32_t bg_coeff = background_gain[idx];
  fg_r[idx] = corrected_state_from_q24(mu_f_r_q24, residual_r_q24, fg_coeff);
  fg_g[idx] = corrected_state_from_q24(mu_f_g_q24, residual_g_q24, fg_coeff);
  fg_b[idx] = corrected_state_from_q24(mu_f_b_q24, residual_b_q24, fg_coeff);
  bg_r[idx] = corrected_state_from_q24(mu_b_r_q24, residual_r_q24, bg_coeff);
  bg_g[idx] = corrected_state_from_q24(mu_b_g_q24, residual_g_q24, bg_coeff);
  bg_b[idx] = corrected_state_from_q24(mu_b_b_q24, residual_b_q24, bg_coeff);
}

inline void update_red_black_half_step_fx_u8_buffer(
    std::uint16_t *FX_RESTRICT fg_r,
    std::uint16_t *FX_RESTRICT fg_g,
    std::uint16_t *FX_RESTRICT fg_b,
    std::uint16_t *FX_RESTRICT bg_r,
    std::uint16_t *FX_RESTRICT bg_g,
    std::uint16_t *FX_RESTRICT bg_b,
    const std::uint32_t *FX_RESTRICT image_r,
    const std::uint32_t *FX_RESTRICT image_g,
    const std::uint32_t *FX_RESTRICT image_b,
    const std::uint8_t *FX_RESTRICT alpha,
    const std::uint8_t *FX_RESTRICT branch_mode,
    const std::uint16_t *FX_RESTRICT neighbor_weights,
    const std::uint32_t *FX_RESTRICT inverse_weight_sum,
    const std::uint32_t *FX_RESTRICT inverse_weight_sum_plus_one,
    const std::uint32_t *FX_RESTRICT foreground_gain,
    const std::uint32_t *FX_RESTRICT background_gain,
    int h,
    int w,
    int color
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  if (h > 2 && w > 2) {
    for (int y = 1; y < h - 1; ++y) {
      const std::size_t row_offset = static_cast<std::size_t>(y) * static_cast<std::size_t>(w);
      int x_start = (color + y) % 2;
      x_start = x_start == 0 ? 2 : 1;
      #if defined(__GNUC__) || defined(__clang__)
      #pragma GCC ivdep
      #endif
      for (int x = x_start; x < w - 1; x += 2) {
        const std::size_t idx = row_offset + static_cast<std::size_t>(x);
        update_pixel_fx_u8(
            idx,
            idx - 1u,
            idx + 1u,
            idx - static_cast<std::size_t>(w),
            idx + static_cast<std::size_t>(w),
            fg_r,
            fg_g,
            fg_b,
            bg_r,
            bg_g,
            bg_b,
            image_r,
            image_g,
            image_b,
            alpha,
            branch_mode,
            neighbor_weights,
            inverse_weight_sum,
            inverse_weight_sum_plus_one,
            foreground_gain,
            background_gain);
      }
    }
  }

  for (int y = 0; y < h; ++y) {
    if (y != 0 && y + 1 < h) {
      continue;
    }
    const int x_start = (color + y) % 2;
    for (int x = x_start; x < w; x += 2) {
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;
      const int y_up = y == 0 ? 0 : y - 1;
      const int y_down = y + 1 >= h ? h - 1 : y + 1;
      const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      update_pixel_fx_u8(
          idx,
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w)),
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w)),
          scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w)),
          scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w)),
          fg_r,
          fg_g,
          fg_b,
          bg_r,
          bg_g,
          bg_b,
          image_r,
          image_g,
          image_b,
          alpha,
          branch_mode,
          neighbor_weights,
          inverse_weight_sum,
          inverse_weight_sum_plus_one,
          foreground_gain,
          background_gain);
    }
  }

  for (int y = 1; y < h - 1; ++y) {
    const int y_up = y - 1;
    const int y_down = y + 1;
    if (((color + y) % 2) == 0) {
      const std::size_t idx = scalar_index(static_cast<std::size_t>(y), 0u, static_cast<std::size_t>(w));
      update_pixel_fx_u8(
          idx,
          idx,
          idx + 1u,
          scalar_index(static_cast<std::size_t>(y_up), 0u, static_cast<std::size_t>(w)),
          scalar_index(static_cast<std::size_t>(y_down), 0u, static_cast<std::size_t>(w)),
          fg_r,
          fg_g,
          fg_b,
          bg_r,
          bg_g,
          bg_b,
          image_r,
          image_g,
          image_b,
          alpha,
          branch_mode,
          neighbor_weights,
          inverse_weight_sum,
          inverse_weight_sum_plus_one,
          foreground_gain,
          background_gain);
    }
    if (w > 1 && ((w - 1 + y) % 2) == color) {
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(w - 1), static_cast<std::size_t>(w));
      update_pixel_fx_u8(
          idx,
          idx - 1u,
          idx,
          scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(w - 1), static_cast<std::size_t>(w)),
          scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(w - 1), static_cast<std::size_t>(w)),
          fg_r,
          fg_g,
          fg_b,
          bg_r,
          bg_g,
          bg_b,
          image_r,
          image_g,
          image_b,
          alpha,
          branch_mode,
          neighbor_weights,
          inverse_weight_sum,
          inverse_weight_sum_plus_one,
          foreground_gain,
          background_gain);
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

  for (int c = 0; c < 3; ++c) {
    workspace.previous_foreground_storage[c][0] = static_cast<std::uint16_t>(fg_mean[c]) << kFxStateFracBits;
    workspace.previous_background_storage[c][0] = static_cast<std::uint16_t>(bg_mean[c]) << kFxStateFracBits;
  }

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
    resize_nearest_rgb_u8_to_image_terms(
        workspace.image_term[0].data(),
        workspace.image_term[1].data(),
        workspace.image_term[2].data(),
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

    const std::size_t pixel_count = static_cast<std::size_t>(h) * static_cast<std::size_t>(w);

    build_level_solver_coefficients_fx_u8_buffer(workspace, h, w);

    workspace.previous_x_index_map.resize(w);
    workspace.previous_y_index_map.resize(h);
    build_resize_index_map_buffer(prev_w, workspace.previous_x_index_map);
    build_resize_index_map_buffer(prev_h, workspace.previous_y_index_map);

    for (int c = 0; c < 3; ++c) {
      resize_nearest_planar_u16_buffer(
          workspace.current_foreground_storage[c].data(),
          workspace.previous_foreground_storage[c].data(),
          workspace.previous_x_index_map.data(),
          workspace.previous_y_index_map.data(),
          prev_w,
          h,
          w);
      resize_nearest_planar_u16_buffer(
          workspace.current_background_storage[c].data(),
          workspace.previous_background_storage[c].data(),
          workspace.previous_x_index_map.data(),
          workspace.previous_y_index_map.data(),
          prev_w,
          h,
          w);
    }

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_red_black_half_step_fx_u8_buffer(
          workspace.current_foreground_storage[0].data(),
          workspace.current_foreground_storage[1].data(),
          workspace.current_foreground_storage[2].data(),
          workspace.current_background_storage[0].data(),
          workspace.current_background_storage[1].data(),
          workspace.current_background_storage[2].data(),
          workspace.image_term[0].data(),
          workspace.image_term[1].data(),
          workspace.image_term[2].data(),
          workspace.alpha.data(),
          workspace.branch_mode.data(),
          workspace.neighbor_weights.data(),
          workspace.inverse_weight_sum.data(),
          workspace.inverse_weight_sum_plus_one.data(),
          workspace.foreground_gain.data(),
          workspace.background_gain.data(),
          h,
          w,
          0);
      update_red_black_half_step_fx_u8_buffer(
          workspace.current_foreground_storage[0].data(),
          workspace.current_foreground_storage[1].data(),
          workspace.current_foreground_storage[2].data(),
          workspace.current_background_storage[0].data(),
          workspace.current_background_storage[1].data(),
          workspace.current_background_storage[2].data(),
          workspace.image_term[0].data(),
          workspace.image_term[1].data(),
          workspace.image_term[2].data(),
          workspace.alpha.data(),
          workspace.branch_mode.data(),
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
      auto *foreground_ptr = foreground_out.data();
      auto *background_ptr = background_out.data();
      for (std::size_t i = 0; i < pixel_count; ++i) {
        foreground_ptr[i * 3u + 0] = quantize_state_to_u8(workspace.current_foreground_storage[0][i]);
        foreground_ptr[i * 3u + 1] = quantize_state_to_u8(workspace.current_foreground_storage[1][i]);
        foreground_ptr[i * 3u + 2] = quantize_state_to_u8(workspace.current_foreground_storage[2][i]);
        background_ptr[i * 3u + 0] = quantize_state_to_u8(workspace.current_background_storage[0][i]);
        background_ptr[i * 3u + 1] = quantize_state_to_u8(workspace.current_background_storage[1][i]);
        background_ptr[i * 3u + 2] = quantize_state_to_u8(workspace.current_background_storage[2][i]);
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

#undef FX_ALWAYS_INLINE
#undef FX_RESTRICT
