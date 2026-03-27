#pragma once

#include "common.hpp"
#include "resize_ops.hpp"
#include "soa_workspace.hpp"

namespace {

struct CurrentLevelSource {
  ConstRgbView foreground;
  ConstRgbView background;

  float read_foreground(int, int, int sample_y, int sample_x, std::size_t c) const {
    return foreground(sample_y, sample_x, c);
  }

  float read_background(int, int, int sample_y, int sample_x, std::size_t c) const {
    return background(sample_y, sample_x, c);
  }
};

struct PreviousLevelBoundarySource {
  ConstRgbView foreground;
  ConstRgbView background;
  ConstRgbView previous_foreground;
  ConstRgbView previous_background;
  const std::int32_t *x_index_map;
  const std::int32_t *y_index_map;

  float read_foreground(int y, int x, int sample_y, int sample_x, std::size_t c) const {
    if (sample_y == y && sample_x == x) {
      return previous_foreground(y_index_map[y], x_index_map[x], c);
    }
    return foreground(sample_y, sample_x, c);
  }

  float read_background(int y, int x, int sample_y, int sample_x, std::size_t c) const {
    if (sample_y == y && sample_x == x) {
      return previous_background(y_index_map[y], x_index_map[x], c);
    }
    return background(sample_y, sample_x, c);
  }
};

template <typename MutableForegroundView, typename MutableBackgroundView>
inline void write_solution(
    MutableForegroundView foreground,
    MutableBackgroundView background,
    std::size_t idx,
    const PixelSolutionInputs &inputs
) {
  const float alpha1 = 1.0f - inputs.alpha;
  const float mu_F0 = inputs.foreground_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_F1 = inputs.foreground_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_F2 = inputs.foreground_weighted_sum_b * inputs.inverse_weight_sum;
  const float mu_B0 = inputs.background_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_B1 = inputs.background_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_B2 = inputs.background_weighted_sum_b * inputs.inverse_weight_sum;

  const float r0 = inputs.image_r - inputs.alpha * mu_F0 - alpha1 * mu_B0;
  const float r1 = inputs.image_g - inputs.alpha * mu_F1 - alpha1 * mu_B1;
  const float r2 = inputs.image_b - inputs.alpha * mu_F2 - alpha1 * mu_B2;

  float *foreground_px = foreground.pixel(idx);
  float *background_px = background.pixel(idx);

  if (inputs.alpha < kAlphaLowThreshold) {
    foreground_px[0] = clamp01(mu_F0);
    foreground_px[1] = clamp01(mu_F1);
    foreground_px[2] = clamp01(mu_F2);
    background_px[0] = clamp01(mu_B0 + r0 * inputs.inverse_weight_sum_plus_one);
    background_px[1] = clamp01(mu_B1 + r1 * inputs.inverse_weight_sum_plus_one);
    background_px[2] = clamp01(mu_B2 + r2 * inputs.inverse_weight_sum_plus_one);
  } else if (inputs.alpha > kAlphaHighThreshold) {
    foreground_px[0] = clamp01(mu_F0 + r0 * inputs.inverse_weight_sum_plus_one);
    foreground_px[1] = clamp01(mu_F1 + r1 * inputs.inverse_weight_sum_plus_one);
    foreground_px[2] = clamp01(mu_F2 + r2 * inputs.inverse_weight_sum_plus_one);
    background_px[0] = clamp01(mu_B0);
    background_px[1] = clamp01(mu_B1);
    background_px[2] = clamp01(mu_B2);
  } else {
    foreground_px[0] = clamp01(mu_F0 + inputs.foreground_gain * r0);
    foreground_px[1] = clamp01(mu_F1 + inputs.foreground_gain * r1);
    foreground_px[2] = clamp01(mu_F2 + inputs.foreground_gain * r2);
    background_px[0] = clamp01(mu_B0 + inputs.background_gain * r0);
    background_px[1] = clamp01(mu_B1 + inputs.background_gain * r1);
    background_px[2] = clamp01(mu_B2 + inputs.background_gain * r2);
  }
}

template <typename AlphaView>
inline void compute_initial_means(AlphaView alpha, ConstRgbView image, int h, int w, float *fg_mean, float *bg_mean) {
  double fg_sum[kChannels] {};
  double bg_sum[kChannels] {};
  int fg_count = 0;
  int bg_count = 0;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const float alpha0 = alpha(y, x);
      if (alpha0 > kInitialForegroundThreshold) {
        for (int c : kChannelIndices) {
          fg_sum[c] += image(y, x, static_cast<std::size_t>(c));
        }
        ++fg_count;
      }
      if (alpha0 < kInitialBackgroundThreshold) {
        for (int c : kChannelIndices) {
          bg_sum[c] += image(y, x, static_cast<std::size_t>(c));
        }
        ++bg_count;
      }
    }
  }

  for (int c : kChannelIndices) {
    fg_mean[c] = fg_count > 0 ? static_cast<float>(fg_sum[c] / fg_count) : 0.0f;
    bg_mean[c] = bg_count > 0 ? static_cast<float>(bg_sum[c] / bg_count) : 0.0f;
  }
}

template <typename AlphaView>
inline void build_level_solver_coefficients_impl(
    AlphaView alpha,
    int h,
    int w,
    float regularization,
    float gradient_weight,
    MutableCoeffView neighbor_weights,
    MutableScalarView inverse_weight_sum,
    MutableScalarView inverse_weight_sum_plus_one,
    MutableScalarView foreground_gain,
    MutableScalarView background_gain
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  const int h_max = h - 1;
  const int w_max = w - 1;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const float alpha0 = alpha(y, x);
      const float alpha1 = 1.0f - alpha0;

      for (int n : kNeighborIndices) {
        const NeighborOffset offset = kNeighborOffsets[n];
        const int sample_y = clamp_index(y + offset.dy, h_max);
        const int sample_x = clamp_index(x + offset.dx, w_max);
        neighbor_weights(y, x, static_cast<std::size_t>(n)) =
            regularization + gradient_weight * std::fabs(alpha0 - alpha(sample_y, sample_x));
      }

      const float *nw = neighbor_weights.pixel(
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w)));
      const float W = nw[0] + nw[1] + nw[2] + nw[3];
      inverse_weight_sum(y, x) = 1.0f / W;
      inverse_weight_sum_plus_one(y, x) = 1.0f / (W + 1.0f);

      const float D = W + alpha0 * alpha0 + alpha1 * alpha1;
      const float inv_D = 1.0f / D;
      foreground_gain(y, x) = alpha0 * inv_D;
      background_gain(y, x) = alpha1 * inv_D;
    }
  }
}

template <SweepColor Color, typename SourcePolicy>
inline void update_red_black_half_step_impl(
    MutableRgbView foreground,
    MutableRgbView background,
    ConstRgbView image,
    ConstScalarView alpha,
    const float *neighbor_weights,
    ConstScalarView inverse_weight_sum,
    ConstScalarView inverse_weight_sum_plus_one,
    ConstScalarView foreground_gain,
    ConstScalarView background_gain,
    int h,
    int w,
    const SourcePolicy &source
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  const int h_max = h - 1;
  const int w_max = w - 1;
  constexpr int parity = static_cast<int>(Color);

  for (int y = 0; y < h; ++y) {
    const int x_start = (parity + y) % 2;
    for (int x = x_start; x < w; x += 2) {
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      const float *nw = neighbor_weights + idx * kNeighborCount;
      float fg_sum[kChannels] {};
      float bg_sum[kChannels] {};

      for (int n : kNeighborIndices) {
        const NeighborOffset offset = kNeighborOffsets[n];
        const int sample_y = clamp_index(y + offset.dy, h_max);
        const int sample_x = clamp_index(x + offset.dx, w_max);
        for (int c : kChannelIndices) {
          const std::size_t channel = static_cast<std::size_t>(c);
          fg_sum[c] += nw[n] * source.read_foreground(y, x, sample_y, sample_x, channel);
          bg_sum[c] += nw[n] * source.read_background(y, x, sample_y, sample_x, channel);
        }
      }

      const PixelSolutionInputs inputs {
          .alpha = alpha(y, x),
          .image_r = image(y, x, 0),
          .image_g = image(y, x, 1),
          .image_b = image(y, x, 2),
          .foreground_weighted_sum_r = fg_sum[0],
          .foreground_weighted_sum_g = fg_sum[1],
          .foreground_weighted_sum_b = fg_sum[2],
          .background_weighted_sum_r = bg_sum[0],
          .background_weighted_sum_g = bg_sum[1],
          .background_weighted_sum_b = bg_sum[2],
          .inverse_weight_sum = inverse_weight_sum(y, x),
          .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one(y, x),
          .foreground_gain = foreground_gain(y, x),
          .background_gain = background_gain(y, x),
      };
      write_solution(foreground, background, idx, inputs);
    }
  }
}

inline void build_level_solver_coefficients_buffer(
    const float *alpha,
    int h,
    int w,
    float regularization,
    float gradient_weight,
    float *neighbor_weights,
    float *inverse_weight_sum,
    float *inverse_weight_sum_plus_one,
    float *foreground_gain,
    float *background_gain
) {
  build_level_solver_coefficients_impl(
      ConstScalarView {.data = alpha, .width = w},
      h,
      w,
      regularization,
      gradient_weight,
      MutableCoeffView {.data = neighbor_weights, .width = w},
      MutableScalarView {.data = inverse_weight_sum, .width = w},
      MutableScalarView {.data = inverse_weight_sum_plus_one, .width = w},
      MutableScalarView {.data = foreground_gain, .width = w},
      MutableScalarView {.data = background_gain, .width = w});
}

inline void build_level_solver_coefficients(
    Alpha alpha,
    float regularization,
    float gradient_weight,
    Coeff4 neighbor_weights,
    MutableAlpha inverse_weight_sum,
    MutableAlpha inverse_weight_sum_plus_one,
    MutableAlpha foreground_gain,
    MutableAlpha background_gain
) {
  const int h = static_cast<int>(alpha.shape(0));
  const int w = static_cast<int>(alpha.shape(1));
  build_level_solver_coefficients_impl(
      ConstScalarView {.data = alpha.data(), .width = w},
      h,
      w,
      regularization,
      gradient_weight,
      MutableCoeffView {.data = neighbor_weights.data(), .width = w},
      MutableScalarView {.data = inverse_weight_sum.data(), .width = w},
      MutableScalarView {.data = inverse_weight_sum_plus_one.data(), .width = w},
      MutableScalarView {.data = foreground_gain.data(), .width = w},
      MutableScalarView {.data = background_gain.data(), .width = w});
}

inline void update_red_black_half_step_buffer(
    float *foreground,
    float *background,
    const float *image,
    const float *alpha,
    const float *neighbor_weights,
    const float *inverse_weight_sum,
    const float *inverse_weight_sum_plus_one,
    const float *foreground_gain,
    const float *background_gain,
    int h,
    int w,
    int color
) {
  const CurrentLevelSource source {
      .foreground = ConstRgbView {.data = foreground, .width = w},
      .background = ConstRgbView {.data = background, .width = w},
  };
  auto fg_view = MutableRgbView {.data = foreground, .width = w};
  auto bg_view = MutableRgbView {.data = background, .width = w};
  auto image_view = ConstRgbView {.data = image, .width = w};
  auto alpha_view = ConstScalarView {.data = alpha, .width = w};
  auto inv_sum_view = ConstScalarView {.data = inverse_weight_sum, .width = w};
  auto inv_sum_plus_one_view = ConstScalarView {.data = inverse_weight_sum_plus_one, .width = w};
  auto fg_gain_view = ConstScalarView {.data = foreground_gain, .width = w};
  auto bg_gain_view = ConstScalarView {.data = background_gain, .width = w};

  if (color == static_cast<int>(SweepColor::red)) {
    update_red_black_half_step_impl<SweepColor::red>(
        fg_view, bg_view, image_view, alpha_view, neighbor_weights, inv_sum_view, inv_sum_plus_one_view, fg_gain_view, bg_gain_view, h, w, source);
  } else {
    update_red_black_half_step_impl<SweepColor::black>(
        fg_view, bg_view, image_view, alpha_view, neighbor_weights, inv_sum_view, inv_sum_plus_one_view, fg_gain_view, bg_gain_view, h, w, source);
  }
}

inline void write_solution_planar(
    MutablePlanarRgbView foreground,
    MutablePlanarRgbView background,
    int y,
    int x,
    const PixelSolutionInputs &inputs
) {
  const float alpha1 = 1.0f - inputs.alpha;
  const float mu_F0 = inputs.foreground_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_F1 = inputs.foreground_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_F2 = inputs.foreground_weighted_sum_b * inputs.inverse_weight_sum;
  const float mu_B0 = inputs.background_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_B1 = inputs.background_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_B2 = inputs.background_weighted_sum_b * inputs.inverse_weight_sum;

  const float r0 = inputs.image_r - inputs.alpha * mu_F0 - alpha1 * mu_B0;
  const float r1 = inputs.image_g - inputs.alpha * mu_F1 - alpha1 * mu_B1;
  const float r2 = inputs.image_b - inputs.alpha * mu_F2 - alpha1 * mu_B2;

  if (inputs.alpha < kAlphaLowThreshold) {
    foreground(y, x, 0) = clamp01(mu_F0);
    foreground(y, x, 1) = clamp01(mu_F1);
    foreground(y, x, 2) = clamp01(mu_F2);
    background(y, x, 0) = clamp01(mu_B0 + r0 * inputs.inverse_weight_sum_plus_one);
    background(y, x, 1) = clamp01(mu_B1 + r1 * inputs.inverse_weight_sum_plus_one);
    background(y, x, 2) = clamp01(mu_B2 + r2 * inputs.inverse_weight_sum_plus_one);
  } else if (inputs.alpha > kAlphaHighThreshold) {
    foreground(y, x, 0) = clamp01(mu_F0 + r0 * inputs.inverse_weight_sum_plus_one);
    foreground(y, x, 1) = clamp01(mu_F1 + r1 * inputs.inverse_weight_sum_plus_one);
    foreground(y, x, 2) = clamp01(mu_F2 + r2 * inputs.inverse_weight_sum_plus_one);
    background(y, x, 0) = clamp01(mu_B0);
    background(y, x, 1) = clamp01(mu_B1);
    background(y, x, 2) = clamp01(mu_B2);
  } else {
    foreground(y, x, 0) = clamp01(mu_F0 + inputs.foreground_gain * r0);
    foreground(y, x, 1) = clamp01(mu_F1 + inputs.foreground_gain * r1);
    foreground(y, x, 2) = clamp01(mu_F2 + inputs.foreground_gain * r2);
    background(y, x, 0) = clamp01(mu_B0 + inputs.background_gain * r0);
    background(y, x, 1) = clamp01(mu_B1 + inputs.background_gain * r1);
    background(y, x, 2) = clamp01(mu_B2 + inputs.background_gain * r2);
  }
}

inline void build_level_solver_coefficients_planar(
    ConstPlaneView alpha,
    int h,
    int w,
    float regularization,
    float gradient_weight,
    PlanarCoeffView coeffs
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  const int h_max = h - 1;
  const int w_max = w - 1;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const float alpha0 = alpha(y, x);
      const float alpha1 = 1.0f - alpha0;

      for (int n : kNeighborIndices) {
        const NeighborOffset offset = kNeighborOffsets[n];
        const int sample_y = clamp_index(y + offset.dy, h_max);
        const int sample_x = clamp_index(x + offset.dx, w_max);
        coeffs.neighbor(y, x, static_cast<std::size_t>(n)) =
            regularization + gradient_weight * std::fabs(alpha0 - alpha(sample_y, sample_x));
      }

      const float W = coeffs.neighbor(y, x, 0) + coeffs.neighbor(y, x, 1) + coeffs.neighbor(y, x, 2) + coeffs.neighbor(y, x, 3);
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(coeffs.stride));
      coeffs.inverse_weight_sum[idx] = 1.0f / W;
      coeffs.inverse_weight_sum_plus_one[idx] = 1.0f / (W + 1.0f);

      const float D = W + alpha0 * alpha0 + alpha1 * alpha1;
      const float inv_D = 1.0f / D;
      coeffs.foreground_gain[idx] = alpha0 * inv_D;
      coeffs.background_gain[idx] = alpha1 * inv_D;
    }
  }
}

template <typename ForegroundView, typename BackgroundView>
inline void accumulate_boundary_sums(
    ForegroundView foreground,
    BackgroundView background,
    ConstPlanarCoeffView coeffs,
    int h,
    int w,
    int y,
    int x,
    float *fg_sum,
    float *bg_sum
) {
  const int h_max = h - 1;
  const int w_max = w - 1;
  fg_sum[0] = 0.0f;
  fg_sum[1] = 0.0f;
  fg_sum[2] = 0.0f;
  bg_sum[0] = 0.0f;
  bg_sum[1] = 0.0f;
  bg_sum[2] = 0.0f;

  for (int n : kNeighborIndices) {
    const NeighborOffset offset = kNeighborOffsets[n];
    const int sample_y = clamp_index(y + offset.dy, h_max);
    const int sample_x = clamp_index(x + offset.dx, w_max);
    const float weight = coeffs.neighbor(y, x, static_cast<std::size_t>(n));
    for (int c : kChannelIndices) {
      const std::size_t channel = static_cast<std::size_t>(c);
      fg_sum[c] += weight * foreground(sample_y, sample_x, channel);
      bg_sum[c] += weight * background(sample_y, sample_x, channel);
    }
  }
}

template <SweepColor Color>
inline void update_red_black_half_step_planar(
    MutablePlanarRgbView foreground,
    MutablePlanarRgbView background,
    ConstPlanarRgbView image,
    ConstPlaneView alpha,
    ConstPlanarCoeffView coeffs,
    int h,
    int w
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  constexpr int parity = static_cast<int>(Color);

  for (int y = 0; y < h; ++y) {
    const int x_start = (parity + y) % 2;

    if (y == 0 || y == h - 1 || w <= 2) {
      for (int x = x_start; x < w; x += 2) {
        float fg_sum[kChannels] {};
        float bg_sum[kChannels] {};
        accumulate_boundary_sums(foreground, background, coeffs, h, w, y, x, fg_sum, bg_sum);
        const std::size_t idx =
            scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(coeffs.stride));
        write_solution_planar(
            foreground,
            background,
            y,
            x,
            PixelSolutionInputs {
                .alpha = alpha(y, x),
                .image_r = image(y, x, 0),
                .image_g = image(y, x, 1),
                .image_b = image(y, x, 2),
                .foreground_weighted_sum_r = fg_sum[0],
                .foreground_weighted_sum_g = fg_sum[1],
                .foreground_weighted_sum_b = fg_sum[2],
                .background_weighted_sum_r = bg_sum[0],
                .background_weighted_sum_g = bg_sum[1],
                .background_weighted_sum_b = bg_sum[2],
                .inverse_weight_sum = coeffs.inverse_weight_sum[idx],
                .inverse_weight_sum_plus_one = coeffs.inverse_weight_sum_plus_one[idx],
                .foreground_gain = coeffs.foreground_gain[idx],
                .background_gain = coeffs.background_gain[idx],
            });
      }
      continue;
    }

    if (x_start == 0) {
      float fg_sum[kChannels] {};
      float bg_sum[kChannels] {};
      accumulate_boundary_sums(foreground, background, coeffs, h, w, y, 0, fg_sum, bg_sum);
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), 0, static_cast<std::size_t>(coeffs.stride));
      write_solution_planar(
          foreground,
          background,
          y,
          0,
          PixelSolutionInputs {
              .alpha = alpha(y, 0),
              .image_r = image(y, 0, 0),
              .image_g = image(y, 0, 1),
              .image_b = image(y, 0, 2),
              .foreground_weighted_sum_r = fg_sum[0],
              .foreground_weighted_sum_g = fg_sum[1],
              .foreground_weighted_sum_b = fg_sum[2],
              .background_weighted_sum_r = bg_sum[0],
              .background_weighted_sum_g = bg_sum[1],
              .background_weighted_sum_b = bg_sum[2],
              .inverse_weight_sum = coeffs.inverse_weight_sum[idx],
              .inverse_weight_sum_plus_one = coeffs.inverse_weight_sum_plus_one[idx],
              .foreground_gain = coeffs.foreground_gain[idx],
              .background_gain = coeffs.background_gain[idx],
          });
    }

    const int interior_start = (x_start == 0) ? 2 : 1;
    for (int x = interior_start; x < w - 1; x += 2) {
      const float w_left = coeffs.neighbor(y, x, 0);
      const float w_right = coeffs.neighbor(y, x, 1);
      const float w_up = coeffs.neighbor(y, x, 2);
      const float w_down = coeffs.neighbor(y, x, 3);

      float fg_sum[kChannels] {};
      float bg_sum[kChannels] {};
      for (int c : kChannelIndices) {
        const std::size_t channel = static_cast<std::size_t>(c);
        fg_sum[c] = w_left * foreground(y, x - 1, channel) + w_right * foreground(y, x + 1, channel) +
                    w_up * foreground(y - 1, x, channel) + w_down * foreground(y + 1, x, channel);
        bg_sum[c] = w_left * background(y, x - 1, channel) + w_right * background(y, x + 1, channel) +
                    w_up * background(y - 1, x, channel) + w_down * background(y + 1, x, channel);
      }

      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(coeffs.stride));
      write_solution_planar(
          foreground,
          background,
          y,
          x,
          PixelSolutionInputs {
              .alpha = alpha(y, x),
              .image_r = image(y, x, 0),
              .image_g = image(y, x, 1),
              .image_b = image(y, x, 2),
              .foreground_weighted_sum_r = fg_sum[0],
              .foreground_weighted_sum_g = fg_sum[1],
              .foreground_weighted_sum_b = fg_sum[2],
              .background_weighted_sum_r = bg_sum[0],
              .background_weighted_sum_g = bg_sum[1],
              .background_weighted_sum_b = bg_sum[2],
              .inverse_weight_sum = coeffs.inverse_weight_sum[idx],
              .inverse_weight_sum_plus_one = coeffs.inverse_weight_sum_plus_one[idx],
              .foreground_gain = coeffs.foreground_gain[idx],
              .background_gain = coeffs.background_gain[idx],
          });
    }

    if (((w - 1) & 1) == x_start) {
      const int x = w - 1;
      float fg_sum[kChannels] {};
      float bg_sum[kChannels] {};
      accumulate_boundary_sums(foreground, background, coeffs, h, w, y, x, fg_sum, bg_sum);
      const std::size_t idx =
          scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(coeffs.stride));
      write_solution_planar(
          foreground,
          background,
          y,
          x,
          PixelSolutionInputs {
              .alpha = alpha(y, x),
              .image_r = image(y, x, 0),
              .image_g = image(y, x, 1),
              .image_b = image(y, x, 2),
              .foreground_weighted_sum_r = fg_sum[0],
              .foreground_weighted_sum_g = fg_sum[1],
              .foreground_weighted_sum_b = fg_sum[2],
              .background_weighted_sum_r = bg_sum[0],
              .background_weighted_sum_g = bg_sum[1],
              .background_weighted_sum_b = bg_sum[2],
              .inverse_weight_sum = coeffs.inverse_weight_sum[idx],
              .inverse_weight_sum_plus_one = coeffs.inverse_weight_sum_plus_one[idx],
              .foreground_gain = coeffs.foreground_gain[idx],
              .background_gain = coeffs.background_gain[idx],
          });
    }
  }
}

inline void estimate_multilevel_foreground_background(
    MutableImage foreground_out,
    MutableImage background_out,
    Image input_image,
    Alpha input_alpha,
    float regularization,
    float gradient_weight,
    int n_small_iterations,
    int n_big_iterations,
    int small_size
) {
  const int h0 = static_cast<int>(input_image.shape(0));
  const int w0 = static_cast<int>(input_image.shape(1));
  validate_float_outputs(foreground_out, background_out, h0, w0);
  if (h0 <= 0 || w0 <= 0) {
    throw std::runtime_error("estimate_multilevel_foreground_background: input image must be non-empty");
  }

  nb::gil_scoped_release release;

  FloatWorkspace &workspace = thread_workspace();
  workspace.ensure_capacity(h0, w0);

  const ConstRgbView input_image_view {.data = input_image.data(), .width = w0};
  const ConstScalarView input_alpha_view {.data = input_alpha.data(), .width = w0};

  float fg_mean[kChannels] {};
  float bg_mean[kChannels] {};
  compute_initial_means(input_alpha_view, input_image_view, h0, w0, fg_mean, bg_mean);

  for (int c : kChannelIndices) {
    workspace.previous_foreground.channels[static_cast<std::size_t>(c)][0] = fg_mean[c];
    workspace.previous_background.channels[static_cast<std::size_t>(c)][0] = bg_mean[c];
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

    const MutablePlanarRgbView image_view = workspace.image.mutable_view(workspace.stride);
    const MutablePlaneView alpha_view = workspace.mutable_alpha_view();
    const MutablePlanarRgbView current_foreground = workspace.current_foreground.mutable_view(workspace.stride);
    const MutablePlanarRgbView current_background = workspace.current_background.mutable_view(workspace.stride);
    const ConstPlanarRgbView previous_foreground = workspace.previous_foreground.const_view(workspace.stride);
    const ConstPlanarRgbView previous_background = workspace.previous_background.const_view(workspace.stride);
    const PlanarCoeffView coeffs = workspace.coeffs.mutable_view(workspace.stride);

    resize_nearest_rgb_to_planar(image_view, input_image_view, h0, w0, h, w);
    resize_nearest_plane_buffer(alpha_view, ConstPlaneView {.data = input_alpha.data(), .stride = w0}, h0, w0, h, w);
    build_level_solver_coefficients_planar(
        workspace.const_alpha_view(),
        h,
        w,
        regularization,
        gradient_weight,
        coeffs);

    resize_nearest_planar_rgb(current_foreground, previous_foreground, prev_h, prev_w, h, w);
    resize_nearest_planar_rgb(current_background, previous_background, prev_h, prev_w, h, w);

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_red_black_half_step_planar<SweepColor::red>(
          current_foreground,
          current_background,
          workspace.image.const_view(workspace.stride),
          workspace.const_alpha_view(),
          workspace.coeffs.const_view(workspace.stride),
          h,
          w);
      update_red_black_half_step_planar<SweepColor::black>(
          current_foreground,
          current_background,
          workspace.image.const_view(workspace.stride),
          workspace.const_alpha_view(),
          workspace.coeffs.const_view(workspace.stride),
          h,
          w);
    }

    const bool final_level = i_level == n_levels;
    if (final_level) {
      export_planar_rgb(foreground_out, workspace.current_foreground.const_view(workspace.stride), h, w);
      export_planar_rgb(background_out, workspace.current_background.const_view(workspace.stride), h, w);
    }

    if (!final_level) {
      std::swap(workspace.previous_foreground, workspace.current_foreground);
      std::swap(workspace.previous_background, workspace.current_background);
      prev_h = h;
      prev_w = w;
    }
  }
}

inline void update_red_black_half_step(
    MutableImage foreground,
    MutableImage background,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inverse_weight_sum,
    MutableAlpha inverse_weight_sum_plus_one,
    MutableAlpha foreground_gain,
    MutableAlpha background_gain,
    int h,
    int w,
    int color
) {
  update_red_black_half_step_buffer(
      foreground.data(),
      background.data(),
      image.data(),
      alpha.data(),
      neighbor_weights.data(),
      inverse_weight_sum.data(),
      inverse_weight_sum_plus_one.data(),
      foreground_gain.data(),
      background_gain.data(),
      h,
      w,
      color);
}

inline void update_red_black_half_step_from_previous_level(
    MutableImage foreground,
    MutableImage background,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inverse_weight_sum,
    MutableAlpha inverse_weight_sum_plus_one,
    MutableAlpha foreground_gain,
    MutableAlpha background_gain,
    MutableImage previous_foreground,
    MutableImage previous_background,
    IndexMap x_previous_index_map,
    IndexMap y_previous_index_map,
    int h,
    int w
) {
  const PreviousLevelBoundarySource source {
      .foreground = ConstRgbView {.data = foreground.data(), .width = w},
      .background = ConstRgbView {.data = background.data(), .width = w},
      .previous_foreground = ConstRgbView {.data = previous_foreground.data(), .width = static_cast<int>(previous_foreground.shape(1))},
      .previous_background = ConstRgbView {.data = previous_background.data(), .width = static_cast<int>(previous_background.shape(1))},
      .x_index_map = x_previous_index_map.data(),
      .y_index_map = y_previous_index_map.data(),
  };
  update_red_black_half_step_impl<SweepColor::red>(
      MutableRgbView {.data = foreground.data(), .width = w},
      MutableRgbView {.data = background.data(), .width = w},
      ConstRgbView {.data = image.data(), .width = w},
      ConstScalarView {.data = alpha.data(), .width = w},
      neighbor_weights.data(),
      ConstScalarView {.data = inverse_weight_sum.data(), .width = w},
      ConstScalarView {.data = inverse_weight_sum_plus_one.data(), .width = w},
      ConstScalarView {.data = foreground_gain.data(), .width = w},
      ConstScalarView {.data = background_gain.data(), .width = w},
      h,
      w,
      source);
}

inline void update_red_black_half_step_from_previous_level_with_boundary_fallback(
    MutableImage foreground,
    MutableImage background,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inverse_weight_sum,
    MutableAlpha inverse_weight_sum_plus_one,
    MutableAlpha foreground_gain,
    MutableAlpha background_gain,
    MutableImage previous_foreground,
    MutableImage previous_background,
    IndexMap x_previous_index_map,
    IndexMap y_previous_index_map,
    int h,
    int w
) {
  const PreviousLevelBoundarySource source {
      .foreground = ConstRgbView {.data = foreground.data(), .width = w},
      .background = ConstRgbView {.data = background.data(), .width = w},
      .previous_foreground = ConstRgbView {.data = previous_foreground.data(), .width = static_cast<int>(previous_foreground.shape(1))},
      .previous_background = ConstRgbView {.data = previous_background.data(), .width = static_cast<int>(previous_background.shape(1))},
      .x_index_map = x_previous_index_map.data(),
      .y_index_map = y_previous_index_map.data(),
  };
  update_red_black_half_step_impl<SweepColor::black>(
      MutableRgbView {.data = foreground.data(), .width = w},
      MutableRgbView {.data = background.data(), .width = w},
      ConstRgbView {.data = image.data(), .width = w},
      ConstScalarView {.data = alpha.data(), .width = w},
      neighbor_weights.data(),
      ConstScalarView {.data = inverse_weight_sum.data(), .width = w},
      ConstScalarView {.data = inverse_weight_sum_plus_one.data(), .width = w},
      ConstScalarView {.data = foreground_gain.data(), .width = w},
      ConstScalarView {.data = background_gain.data(), .width = w},
      h,
      w,
      source);
}

}  // namespace
