#pragma once

#include "common.hpp"
#include "resize_ops.hpp"
#include "soa_workspace.hpp"

namespace {

inline float fmadd(float a, float b, float c) {
  return std::fmaf(a, b, c);
}

inline void write_solution(
    MutableImage foreground,
    MutableImage background,
    std::size_t y,
    std::size_t x,
    const PixelSolutionInputs &inputs
) {
  const float alpha1 = 1.0f - inputs.alpha;
  const float mu_F0 = inputs.foreground_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_F1 = inputs.foreground_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_F2 = inputs.foreground_weighted_sum_b * inputs.inverse_weight_sum;
  const float mu_B0 = inputs.background_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_B1 = inputs.background_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_B2 = inputs.background_weighted_sum_b * inputs.inverse_weight_sum;

  const float r0 = fmadd(-alpha1, mu_B0, fmadd(-inputs.alpha, mu_F0, inputs.image_r));
  const float r1 = fmadd(-alpha1, mu_B1, fmadd(-inputs.alpha, mu_F1, inputs.image_g));
  const float r2 = fmadd(-alpha1, mu_B2, fmadd(-inputs.alpha, mu_F2, inputs.image_b));

  if (inputs.alpha < kAlphaLowThreshold) {
    foreground(y, x, 0) = clamp01(mu_F0);
    foreground(y, x, 1) = clamp01(mu_F1);
    foreground(y, x, 2) = clamp01(mu_F2);
    background(y, x, 0) = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r0, mu_B0));
    background(y, x, 1) = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r1, mu_B1));
    background(y, x, 2) = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r2, mu_B2));
  } else if (inputs.alpha > kAlphaHighThreshold) {
    foreground(y, x, 0) = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r0, mu_F0));
    foreground(y, x, 1) = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r1, mu_F1));
    foreground(y, x, 2) = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r2, mu_F2));
    background(y, x, 0) = clamp01(mu_B0);
    background(y, x, 1) = clamp01(mu_B1);
    background(y, x, 2) = clamp01(mu_B2);
  } else {
    foreground(y, x, 0) = clamp01(fmadd(inputs.foreground_gain, r0, mu_F0));
    foreground(y, x, 1) = clamp01(fmadd(inputs.foreground_gain, r1, mu_F1));
    foreground(y, x, 2) = clamp01(fmadd(inputs.foreground_gain, r2, mu_F2));
    background(y, x, 0) = clamp01(fmadd(inputs.background_gain, r0, mu_B0));
    background(y, x, 1) = clamp01(fmadd(inputs.background_gain, r1, mu_B1));
    background(y, x, 2) = clamp01(fmadd(inputs.background_gain, r2, mu_B2));
  }
}

inline void write_solution_buffer(float *foreground, float *background, std::size_t idx, const PixelSolutionInputs &inputs) {
  const float alpha1 = 1.0f - inputs.alpha;
  const float mu_F0 = inputs.foreground_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_F1 = inputs.foreground_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_F2 = inputs.foreground_weighted_sum_b * inputs.inverse_weight_sum;
  const float mu_B0 = inputs.background_weighted_sum_r * inputs.inverse_weight_sum;
  const float mu_B1 = inputs.background_weighted_sum_g * inputs.inverse_weight_sum;
  const float mu_B2 = inputs.background_weighted_sum_b * inputs.inverse_weight_sum;

  const float r0 = fmadd(-alpha1, mu_B0, fmadd(-inputs.alpha, mu_F0, inputs.image_r));
  const float r1 = fmadd(-alpha1, mu_B1, fmadd(-inputs.alpha, mu_F1, inputs.image_g));
  const float r2 = fmadd(-alpha1, mu_B2, fmadd(-inputs.alpha, mu_F2, inputs.image_b));

  float *foreground_px = foreground + idx * kChannels;
  float *background_px = background + idx * kChannels;

  if (inputs.alpha < kAlphaLowThreshold) {
    foreground_px[0] = clamp01(mu_F0);
    foreground_px[1] = clamp01(mu_F1);
    foreground_px[2] = clamp01(mu_F2);
    background_px[0] = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r0, mu_B0));
    background_px[1] = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r1, mu_B1));
    background_px[2] = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r2, mu_B2));
  } else if (inputs.alpha > kAlphaHighThreshold) {
    foreground_px[0] = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r0, mu_F0));
    foreground_px[1] = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r1, mu_F1));
    foreground_px[2] = clamp01(fmadd(inputs.inverse_weight_sum_plus_one, r2, mu_F2));
    background_px[0] = clamp01(mu_B0);
    background_px[1] = clamp01(mu_B1);
    background_px[2] = clamp01(mu_B2);
  } else {
    foreground_px[0] = clamp01(fmadd(inputs.foreground_gain, r0, mu_F0));
    foreground_px[1] = clamp01(fmadd(inputs.foreground_gain, r1, mu_F1));
    foreground_px[2] = clamp01(fmadd(inputs.foreground_gain, r2, mu_F2));
    background_px[0] = clamp01(fmadd(inputs.background_gain, r0, mu_B0));
    background_px[1] = clamp01(fmadd(inputs.background_gain, r1, mu_B1));
    background_px[2] = clamp01(fmadd(inputs.background_gain, r2, mu_B2));
  }
}

inline void compute_initial_means_buffer(const float *image, const float *alpha, int h, int w, float *fg_mean, float *bg_mean) {
  double fg_sum[kChannels] {};
  double bg_sum[kChannels] {};
  int fg_count = 0;
  int bg_count = 0;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      const float alpha0 = alpha[idx];
      const float *px = image + idx * kChannels;
      if (alpha0 > kInitialForegroundThreshold) {
        fg_sum[0] += px[0];
        fg_sum[1] += px[1];
        fg_sum[2] += px[2];
        ++fg_count;
      }
      if (alpha0 < kInitialBackgroundThreshold) {
        bg_sum[0] += px[0];
        bg_sum[1] += px[1];
        bg_sum[2] += px[2];
        ++bg_count;
      }
    }
  }

  for (int c : kChannelIndices) {
    fg_mean[c] = fg_count > 0 ? static_cast<float>(fg_sum[c] / fg_count) : 0.0f;
    bg_mean[c] = bg_count > 0 ? static_cast<float>(bg_sum[c] / bg_count) : 0.0f;
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
  if (h <= 0 || w <= 0) {
    return;
  }

  auto process_pixel = [&](int y, int x) {
    const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const float alpha0 = alpha[idx];
    const float alpha1 = 1.0f - alpha0;
    const int x_left = x == 0 ? 0 : x - 1;
    const int x_right = std::min(w - 1, x + 1);
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = std::min(h - 1, y + 1);

    const float w0 = regularization + gradient_weight * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w))]);
    const float w1 = regularization + gradient_weight * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w))]);
    const float w2 = regularization + gradient_weight * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);
    const float w3 = regularization + gradient_weight * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);

    float *nw = neighbor_weights + idx * kNeighborCount;
    nw[0] = w0;
    nw[1] = w1;
    nw[2] = w2;
    nw[3] = w3;

    const float W = w0 + w1 + w2 + w3;
    inverse_weight_sum[idx] = 1.0f / W;
    inverse_weight_sum_plus_one[idx] = 1.0f / (W + 1.0f);

    const float D = fmadd(alpha1, alpha1, fmadd(alpha0, alpha0, W));
    const float inv_D = 1.0f / D;
    foreground_gain[idx] = alpha0 * inv_D;
    background_gain[idx] = alpha1 * inv_D;
  };

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      process_pixel(y, x);
    }
  }
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
  build_level_solver_coefficients_buffer(
      alpha.data(),
      h,
      w,
      regularization,
      gradient_weight,
      neighbor_weights.data(),
      inverse_weight_sum.data(),
      inverse_weight_sum_plus_one.data(),
      foreground_gain.data(),
      background_gain.data());
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
  if (h <= 0 || w <= 0) {
    return;
  }

  auto process_pixel = [&](int y, int x) {
    const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const int x_left = x == 0 ? 0 : x - 1;
    const int x_right = x + 1 >= w ? w - 1 : x + 1;
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = y + 1 >= h ? h - 1 : y + 1;
    const std::size_t idx_left = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w));
    const std::size_t idx_right = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w));
    const std::size_t idx_up = scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::size_t idx_down = scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const float *nw = neighbor_weights + idx * kNeighborCount;
    const std::size_t image_idx = idx * kChannels;

    const PixelSolutionInputs inputs {
        .alpha = alpha[idx],
        .image_r = image[image_idx + 0],
        .image_g = image[image_idx + 1],
        .image_b = image[image_idx + 2],
        .foreground_weighted_sum_r =
            nw[0] * foreground[idx_left * kChannels + 0] + nw[1] * foreground[idx_right * kChannels + 0] +
            nw[2] * foreground[idx_up * kChannels + 0] + nw[3] * foreground[idx_down * kChannels + 0],
        .foreground_weighted_sum_g =
            nw[0] * foreground[idx_left * kChannels + 1] + nw[1] * foreground[idx_right * kChannels + 1] +
            nw[2] * foreground[idx_up * kChannels + 1] + nw[3] * foreground[idx_down * kChannels + 1],
        .foreground_weighted_sum_b =
            nw[0] * foreground[idx_left * kChannels + 2] + nw[1] * foreground[idx_right * kChannels + 2] +
            nw[2] * foreground[idx_up * kChannels + 2] + nw[3] * foreground[idx_down * kChannels + 2],
        .background_weighted_sum_r =
            nw[0] * background[idx_left * kChannels + 0] + nw[1] * background[idx_right * kChannels + 0] +
            nw[2] * background[idx_up * kChannels + 0] + nw[3] * background[idx_down * kChannels + 0],
        .background_weighted_sum_g =
            nw[0] * background[idx_left * kChannels + 1] + nw[1] * background[idx_right * kChannels + 1] +
            nw[2] * background[idx_up * kChannels + 1] + nw[3] * background[idx_down * kChannels + 1],
        .background_weighted_sum_b =
            nw[0] * background[idx_left * kChannels + 2] + nw[1] * background[idx_right * kChannels + 2] +
            nw[2] * background[idx_up * kChannels + 2] + nw[3] * background[idx_down * kChannels + 2],
        .inverse_weight_sum = inverse_weight_sum[idx],
        .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one[idx],
        .foreground_gain = foreground_gain[idx],
        .background_gain = background_gain[idx],
    };
    write_solution_buffer(foreground, background, idx, inputs);
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

  const float *input_image_ptr = input_image.data();
  const float *input_alpha_ptr = input_alpha.data();

  nb::gil_scoped_release release;

  const std::size_t max_pixels = static_cast<std::size_t>(h0) * static_cast<std::size_t>(w0);
  FloatWorkspace &workspace = thread_workspace();
  workspace.ensure_capacity(max_pixels, w0, h0);

  float fg_mean[kChannels] {};
  float bg_mean[kChannels] {};
  compute_initial_means_buffer(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

  workspace.previous_foreground_storage[0] = fg_mean[0];
  workspace.previous_foreground_storage[1] = fg_mean[1];
  workspace.previous_foreground_storage[2] = fg_mean[2];
  workspace.previous_background_storage[0] = bg_mean[0];
  workspace.previous_background_storage[1] = bg_mean[1];
  workspace.previous_background_storage[2] = bg_mean[2];

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

    resize_nearest_rgb_buffer(workspace.image.data(), input_image_ptr, h0, w0, h, w);
    resize_nearest_scalar_buffer(workspace.alpha.data(), input_alpha_ptr, h0, w0, h, w);
    build_level_solver_coefficients_buffer(
        workspace.alpha.data(),
        h,
        w,
        regularization,
        gradient_weight,
        workspace.neighbor_weights.data(),
        workspace.inverse_weight_sum.data(),
        workspace.inverse_weight_sum_plus_one.data(),
        workspace.foreground_gain.data(),
        workspace.background_gain.data());

    const bool final_level = i_level == n_levels;
    float *current_foreground = final_level ? foreground_out.data() : workspace.current_foreground_storage.data();
    float *current_background = final_level ? background_out.data() : workspace.current_background_storage.data();

    resize_nearest_rgb_buffer(current_foreground, workspace.previous_foreground_storage.data(), prev_h, prev_w, h, w);
    resize_nearest_rgb_buffer(current_background, workspace.previous_background_storage.data(), prev_h, prev_w, h, w);

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_red_black_half_step_buffer(
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
          static_cast<int>(SweepColor::red));
      update_red_black_half_step_buffer(
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
          static_cast<int>(SweepColor::black));
    }

    if (!final_level) {
      std::swap(workspace.previous_foreground_storage, workspace.current_foreground_storage);
      std::swap(workspace.previous_background_storage, workspace.current_background_storage);
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
  for (int y = 0; y < h; ++y) {
    const int x_start = (color + y) % 2;
    for (int x = x_start; x < w; x += 2) {
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;
      const int y_up = y == 0 ? 0 : y - 1;
      const int y_down = y + 1 >= h ? h - 1 : y + 1;
      const PixelSolutionInputs inputs {
          .alpha = alpha(y, x),
          .image_r = image(y, x, 0),
          .image_g = image(y, x, 1),
          .image_b = image(y, x, 2),
          .foreground_weighted_sum_r =
              neighbor_weights(y, x, 0) * foreground(y, x_left, 0) + neighbor_weights(y, x, 1) * foreground(y, x_right, 0) +
              neighbor_weights(y, x, 2) * foreground(y_up, x, 0) + neighbor_weights(y, x, 3) * foreground(y_down, x, 0),
          .foreground_weighted_sum_g =
              neighbor_weights(y, x, 0) * foreground(y, x_left, 1) + neighbor_weights(y, x, 1) * foreground(y, x_right, 1) +
              neighbor_weights(y, x, 2) * foreground(y_up, x, 1) + neighbor_weights(y, x, 3) * foreground(y_down, x, 1),
          .foreground_weighted_sum_b =
              neighbor_weights(y, x, 0) * foreground(y, x_left, 2) + neighbor_weights(y, x, 1) * foreground(y, x_right, 2) +
              neighbor_weights(y, x, 2) * foreground(y_up, x, 2) + neighbor_weights(y, x, 3) * foreground(y_down, x, 2),
          .background_weighted_sum_r =
              neighbor_weights(y, x, 0) * background(y, x_left, 0) + neighbor_weights(y, x, 1) * background(y, x_right, 0) +
              neighbor_weights(y, x, 2) * background(y_up, x, 0) + neighbor_weights(y, x, 3) * background(y_down, x, 0),
          .background_weighted_sum_g =
              neighbor_weights(y, x, 0) * background(y, x_left, 1) + neighbor_weights(y, x, 1) * background(y, x_right, 1) +
              neighbor_weights(y, x, 2) * background(y_up, x, 1) + neighbor_weights(y, x, 3) * background(y_down, x, 1),
          .background_weighted_sum_b =
              neighbor_weights(y, x, 0) * background(y, x_left, 2) + neighbor_weights(y, x, 1) * background(y, x_right, 2) +
              neighbor_weights(y, x, 2) * background(y_up, x, 2) + neighbor_weights(y, x, 3) * background(y_down, x, 2),
          .inverse_weight_sum = inverse_weight_sum(y, x),
          .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one(y, x),
          .foreground_gain = foreground_gain(y, x),
          .background_gain = background_gain(y, x),
      };
      write_solution(foreground, background, static_cast<std::size_t>(y), static_cast<std::size_t>(x), inputs);
    }
  }
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
  for (int y = 0; y < h; ++y) {
    const int x_start = y % 2;
    const std::int32_t y_current_prev = y_previous_index_map(y);
    const std::int32_t y_up = y == 0 ? 0 : y - 1;
    const std::int32_t y_down = y + 1 >= h ? h - 1 : y + 1;

    for (int x = x_start; x < w; x += 2) {
      const std::int32_t x_prev = x_previous_index_map(x);
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;

      float foreground_weighted_sum_r = 0.0f;
      float foreground_weighted_sum_g = 0.0f;
      float foreground_weighted_sum_b = 0.0f;
      float background_weighted_sum_r = 0.0f;
      float background_weighted_sum_g = 0.0f;
      float background_weighted_sum_b = 0.0f;

      if (x_left == x) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 0) * previous_foreground(y_current_prev, x_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 0) * previous_foreground(y_current_prev, x_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 0) * previous_foreground(y_current_prev, x_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 0) * previous_background(y_current_prev, x_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 0) * previous_background(y_current_prev, x_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 0) * previous_background(y_current_prev, x_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 0) * foreground(y, x_left, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 0) * foreground(y, x_left, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 0) * foreground(y, x_left, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 0) * background(y, x_left, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 0) * background(y, x_left, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 0) * background(y, x_left, 2);
      }

      if (x_right == x) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 1) * previous_foreground(y_current_prev, x_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 1) * previous_foreground(y_current_prev, x_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 1) * previous_foreground(y_current_prev, x_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 1) * previous_background(y_current_prev, x_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 1) * previous_background(y_current_prev, x_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 1) * previous_background(y_current_prev, x_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 1) * foreground(y, x_right, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 1) * foreground(y, x_right, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 1) * foreground(y, x_right, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 1) * background(y, x_right, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 1) * background(y, x_right, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 1) * background(y, x_right, 2);
      }

      if (y_up == y) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 2) * previous_foreground(y_current_prev, x_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 2) * previous_foreground(y_current_prev, x_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 2) * previous_foreground(y_current_prev, x_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 2) * previous_background(y_current_prev, x_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 2) * previous_background(y_current_prev, x_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 2) * previous_background(y_current_prev, x_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 2) * foreground(y_up, x, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 2) * foreground(y_up, x, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 2) * foreground(y_up, x, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 2) * background(y_up, x, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 2) * background(y_up, x, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 2) * background(y_up, x, 2);
      }

      if (y_down == y) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 3) * previous_foreground(y_current_prev, x_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 3) * previous_foreground(y_current_prev, x_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 3) * previous_foreground(y_current_prev, x_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 3) * previous_background(y_current_prev, x_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 3) * previous_background(y_current_prev, x_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 3) * previous_background(y_current_prev, x_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 3) * foreground(y_down, x, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 3) * foreground(y_down, x, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 3) * foreground(y_down, x, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 3) * background(y_down, x, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 3) * background(y_down, x, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 3) * background(y_down, x, 2);
      }

      const PixelSolutionInputs inputs {
          .alpha = alpha(y, x),
          .image_r = image(y, x, 0),
          .image_g = image(y, x, 1),
          .image_b = image(y, x, 2),
          .foreground_weighted_sum_r = foreground_weighted_sum_r,
          .foreground_weighted_sum_g = foreground_weighted_sum_g,
          .foreground_weighted_sum_b = foreground_weighted_sum_b,
          .background_weighted_sum_r = background_weighted_sum_r,
          .background_weighted_sum_g = background_weighted_sum_g,
          .background_weighted_sum_b = background_weighted_sum_b,
          .inverse_weight_sum = inverse_weight_sum(y, x),
          .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one(y, x),
          .foreground_gain = foreground_gain(y, x),
          .background_gain = background_gain(y, x),
      };
      write_solution(foreground, background, static_cast<std::size_t>(y), static_cast<std::size_t>(x), inputs);
    }
  }
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
  for (int y = 0; y < h; ++y) {
    const int x_start = (static_cast<int>(SweepColor::black) + y) % 2;
    const std::int32_t y_current_prev = y_previous_index_map(y);
    const std::int32_t y_up = y == 0 ? 0 : y - 1;
    const std::int32_t y_down = y + 1 >= h ? h - 1 : y + 1;

    for (int x = x_start; x < w; x += 2) {
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;
      const std::int32_t x_current_prev = x_previous_index_map(x);

      float foreground_weighted_sum_r = 0.0f;
      float foreground_weighted_sum_g = 0.0f;
      float foreground_weighted_sum_b = 0.0f;
      float background_weighted_sum_r = 0.0f;
      float background_weighted_sum_g = 0.0f;
      float background_weighted_sum_b = 0.0f;

      if (x_left == x) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 0) * previous_foreground(y_current_prev, x_current_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 0) * previous_foreground(y_current_prev, x_current_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 0) * previous_foreground(y_current_prev, x_current_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 0) * previous_background(y_current_prev, x_current_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 0) * previous_background(y_current_prev, x_current_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 0) * previous_background(y_current_prev, x_current_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 0) * foreground(y, x_left, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 0) * foreground(y, x_left, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 0) * foreground(y, x_left, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 0) * background(y, x_left, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 0) * background(y, x_left, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 0) * background(y, x_left, 2);
      }

      if (x_right == x) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 1) * previous_foreground(y_current_prev, x_current_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 1) * previous_foreground(y_current_prev, x_current_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 1) * previous_foreground(y_current_prev, x_current_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 1) * previous_background(y_current_prev, x_current_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 1) * previous_background(y_current_prev, x_current_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 1) * previous_background(y_current_prev, x_current_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 1) * foreground(y, x_right, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 1) * foreground(y, x_right, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 1) * foreground(y, x_right, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 1) * background(y, x_right, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 1) * background(y, x_right, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 1) * background(y, x_right, 2);
      }

      if (y_up == y) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 2) * previous_foreground(y_current_prev, x_current_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 2) * previous_foreground(y_current_prev, x_current_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 2) * previous_foreground(y_current_prev, x_current_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 2) * previous_background(y_current_prev, x_current_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 2) * previous_background(y_current_prev, x_current_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 2) * previous_background(y_current_prev, x_current_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 2) * foreground(y_up, x, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 2) * foreground(y_up, x, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 2) * foreground(y_up, x, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 2) * background(y_up, x, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 2) * background(y_up, x, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 2) * background(y_up, x, 2);
      }

      if (y_down == y) {
        foreground_weighted_sum_r += neighbor_weights(y, x, 3) * previous_foreground(y_current_prev, x_current_prev, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 3) * previous_foreground(y_current_prev, x_current_prev, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 3) * previous_foreground(y_current_prev, x_current_prev, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 3) * previous_background(y_current_prev, x_current_prev, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 3) * previous_background(y_current_prev, x_current_prev, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 3) * previous_background(y_current_prev, x_current_prev, 2);
      } else {
        foreground_weighted_sum_r += neighbor_weights(y, x, 3) * foreground(y_down, x, 0);
        foreground_weighted_sum_g += neighbor_weights(y, x, 3) * foreground(y_down, x, 1);
        foreground_weighted_sum_b += neighbor_weights(y, x, 3) * foreground(y_down, x, 2);
        background_weighted_sum_r += neighbor_weights(y, x, 3) * background(y_down, x, 0);
        background_weighted_sum_g += neighbor_weights(y, x, 3) * background(y_down, x, 1);
        background_weighted_sum_b += neighbor_weights(y, x, 3) * background(y_down, x, 2);
      }

      const PixelSolutionInputs inputs {
          .alpha = alpha(y, x),
          .image_r = image(y, x, 0),
          .image_g = image(y, x, 1),
          .image_b = image(y, x, 2),
          .foreground_weighted_sum_r = foreground_weighted_sum_r,
          .foreground_weighted_sum_g = foreground_weighted_sum_g,
          .foreground_weighted_sum_b = foreground_weighted_sum_b,
          .background_weighted_sum_r = background_weighted_sum_r,
          .background_weighted_sum_g = background_weighted_sum_g,
          .background_weighted_sum_b = background_weighted_sum_b,
          .inverse_weight_sum = inverse_weight_sum(y, x),
          .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one(y, x),
          .foreground_gain = foreground_gain(y, x),
          .background_gain = background_gain(y, x),
      };
      write_solution(foreground, background, static_cast<std::size_t>(y), static_cast<std::size_t>(x), inputs);
    }
  }
}

}  // namespace
