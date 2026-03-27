#pragma once

#include "common.hpp"
#include "resize_ops.hpp"

namespace {

inline void write_solution(MutableImage foreground, MutableImage background, std::size_t y, std::size_t x, const PixelSolutionInputs &inputs) {
  const float alpha1 = 1.0f - inputs.alpha;
  const float mu_F0 = inputs.sum_wF0 * inputs.inv_W;
  const float mu_F1 = inputs.sum_wF1 * inputs.inv_W;
  const float mu_F2 = inputs.sum_wF2 * inputs.inv_W;
  const float mu_B0 = inputs.sum_wB0 * inputs.inv_W;
  const float mu_B1 = inputs.sum_wB1 * inputs.inv_W;
  const float mu_B2 = inputs.sum_wB2 * inputs.inv_W;

  const float r0 = inputs.image0 - inputs.alpha * mu_F0 - alpha1 * mu_B0;
  const float r1 = inputs.image1 - inputs.alpha * mu_F1 - alpha1 * mu_B1;
  const float r2 = inputs.image2 - inputs.alpha * mu_F2 - alpha1 * mu_B2;

  if (inputs.alpha < 0.01f) {
    foreground(y, x, 0) = clamp01(mu_F0);
    foreground(y, x, 1) = clamp01(mu_F1);
    foreground(y, x, 2) = clamp01(mu_F2);
    background(y, x, 0) = clamp01(mu_B0 + r0 * inputs.inv_Wp1);
    background(y, x, 1) = clamp01(mu_B1 + r1 * inputs.inv_Wp1);
    background(y, x, 2) = clamp01(mu_B2 + r2 * inputs.inv_Wp1);
  } else if (inputs.alpha > 0.99f) {
    foreground(y, x, 0) = clamp01(mu_F0 + r0 * inputs.inv_Wp1);
    foreground(y, x, 1) = clamp01(mu_F1 + r1 * inputs.inv_Wp1);
    foreground(y, x, 2) = clamp01(mu_F2 + r2 * inputs.inv_Wp1);
    background(y, x, 0) = clamp01(mu_B0);
    background(y, x, 1) = clamp01(mu_B1);
    background(y, x, 2) = clamp01(mu_B2);
  } else {
    foreground(y, x, 0) = clamp01(mu_F0 + inputs.fg_gain * r0);
    foreground(y, x, 1) = clamp01(mu_F1 + inputs.fg_gain * r1);
    foreground(y, x, 2) = clamp01(mu_F2 + inputs.fg_gain * r2);
    background(y, x, 0) = clamp01(mu_B0 + inputs.bg_gain * r0);
    background(y, x, 1) = clamp01(mu_B1 + inputs.bg_gain * r1);
    background(y, x, 2) = clamp01(mu_B2 + inputs.bg_gain * r2);
  }
}

inline void write_solution_raw(float *foreground, float *background, std::size_t idx, const PixelSolutionInputs &inputs) {
  const float alpha1 = 1.0f - inputs.alpha;
  const float mu_F0 = inputs.sum_wF0 * inputs.inv_W;
  const float mu_F1 = inputs.sum_wF1 * inputs.inv_W;
  const float mu_F2 = inputs.sum_wF2 * inputs.inv_W;
  const float mu_B0 = inputs.sum_wB0 * inputs.inv_W;
  const float mu_B1 = inputs.sum_wB1 * inputs.inv_W;
  const float mu_B2 = inputs.sum_wB2 * inputs.inv_W;

  const float r0 = inputs.image0 - inputs.alpha * mu_F0 - alpha1 * mu_B0;
  const float r1 = inputs.image1 - inputs.alpha * mu_F1 - alpha1 * mu_B1;
  const float r2 = inputs.image2 - inputs.alpha * mu_F2 - alpha1 * mu_B2;

  float *F_px = foreground + idx * 3;
  float *B_px = background + idx * 3;

  if (inputs.alpha < 0.01f) {
    F_px[0] = clamp01(mu_F0);
    F_px[1] = clamp01(mu_F1);
    F_px[2] = clamp01(mu_F2);
    B_px[0] = clamp01(mu_B0 + r0 * inputs.inv_Wp1);
    B_px[1] = clamp01(mu_B1 + r1 * inputs.inv_Wp1);
    B_px[2] = clamp01(mu_B2 + r2 * inputs.inv_Wp1);
  } else if (inputs.alpha > 0.99f) {
    F_px[0] = clamp01(mu_F0 + r0 * inputs.inv_Wp1);
    F_px[1] = clamp01(mu_F1 + r1 * inputs.inv_Wp1);
    F_px[2] = clamp01(mu_F2 + r2 * inputs.inv_Wp1);
    B_px[0] = clamp01(mu_B0);
    B_px[1] = clamp01(mu_B1);
    B_px[2] = clamp01(mu_B2);
  } else {
    F_px[0] = clamp01(mu_F0 + inputs.fg_gain * r0);
    F_px[1] = clamp01(mu_F1 + inputs.fg_gain * r1);
    F_px[2] = clamp01(mu_F2 + inputs.fg_gain * r2);
    B_px[0] = clamp01(mu_B0 + inputs.bg_gain * r0);
    B_px[1] = clamp01(mu_B1 + inputs.bg_gain * r1);
    B_px[2] = clamp01(mu_B2 + inputs.bg_gain * r2);
  }
}

inline void compute_initial_means_raw(const float *image, const float *alpha, int h, int w, float *fg_mean, float *bg_mean) {
  double fg_sum[3] {0.0, 0.0, 0.0};
  double bg_sum[3] {0.0, 0.0, 0.0};
  int fg_count = 0;
  int bg_count = 0;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      const float alpha0 = alpha[idx];
      const float *px = image + idx * 3;
      if (alpha0 > 0.9f) {
        fg_sum[0] += px[0];
        fg_sum[1] += px[1];
        fg_sum[2] += px[2];
        ++fg_count;
      }
      if (alpha0 < 0.1f) {
        bg_sum[0] += px[0];
        bg_sum[1] += px[1];
        bg_sum[2] += px[2];
        ++bg_count;
      }
    }
  }

  if (fg_count > 0) {
    fg_mean[0] = static_cast<float>(fg_sum[0] / fg_count);
    fg_mean[1] = static_cast<float>(fg_sum[1] / fg_count);
    fg_mean[2] = static_cast<float>(fg_sum[2] / fg_count);
  } else {
    fg_mean[0] = 0.0f;
    fg_mean[1] = 0.0f;
    fg_mean[2] = 0.0f;
  }

  if (bg_count > 0) {
    bg_mean[0] = static_cast<float>(bg_sum[0] / bg_count);
    bg_mean[1] = static_cast<float>(bg_sum[1] / bg_count);
    bg_mean[2] = static_cast<float>(bg_sum[2] / bg_count);
  } else {
    bg_mean[0] = 0.0f;
    bg_mean[1] = 0.0f;
    bg_mean[2] = 0.0f;
  }
}

inline void build_level_coefficients_raw(
    const float *alpha,
    int h,
    int w,
    float eps,
    float omega,
    float *neighbor_weights,
    float *inv_W,
    float *inv_Wp1,
    float *fg_gain,
    float *bg_gain
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

    const float w0 = eps + omega * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w))]);
    const float w1 = eps + omega * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w))]);
    const float w2 = eps + omega * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);
    const float w3 = eps + omega * std::fabs(alpha0 - alpha[scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);

    float *nw = neighbor_weights + idx * 4;
    nw[0] = w0;
    nw[1] = w1;
    nw[2] = w2;
    nw[3] = w3;

    const float W = w0 + w1 + w2 + w3;
    inv_W[idx] = 1.0f / W;
    inv_Wp1[idx] = 1.0f / (W + 1.0f);

    const float D = W + alpha0 * alpha0 + alpha1 * alpha1;
    const float inv_D = 1.0f / D;
    fg_gain[idx] = alpha0 * inv_D;
    bg_gain[idx] = alpha1 * inv_D;
  };

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      process_pixel(y, x);
    }
  }
}

inline void build_level_coefficients(
    Alpha alpha,
    float eps,
    float omega,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain
) {
  const std::size_t h = alpha.shape(0);
  const std::size_t w = alpha.shape(1);

  for (std::size_t y = 0; y < h; ++y) {
    for (std::size_t x = 0; x < w; ++x) {
      const float alpha0 = alpha(y, x);
      const float alpha1 = 1.0f - alpha0;
      const std::size_t x_left = x == 0 ? 0 : x - 1;
      const std::size_t x_right = std::min(w - 1, x + 1);
      const std::size_t y_up = y == 0 ? 0 : y - 1;
      const std::size_t y_down = std::min(h - 1, y + 1);

      const float w0 = eps + omega * std::fabs(alpha0 - alpha(y, x_left));
      const float w1 = eps + omega * std::fabs(alpha0 - alpha(y, x_right));
      const float w2 = eps + omega * std::fabs(alpha0 - alpha(y_up, x));
      const float w3 = eps + omega * std::fabs(alpha0 - alpha(y_down, x));

      neighbor_weights(y, x, 0) = w0;
      neighbor_weights(y, x, 1) = w1;
      neighbor_weights(y, x, 2) = w2;
      neighbor_weights(y, x, 3) = w3;

      const float W = w0 + w1 + w2 + w3;
      inv_W(y, x) = 1.0f / W;
      inv_Wp1(y, x) = 1.0f / (W + 1.0f);

      const float D = W + alpha0 * alpha0 + alpha1 * alpha1;
      const float inv_D = 1.0f / D;
      fg_gain(y, x) = alpha0 * inv_D;
      bg_gain(y, x) = alpha1 * inv_D;
    }
  }
}

inline void update_rb_half_cached_raw(
    float *foreground,
    float *background,
    const float *image,
    const float *alpha,
    const float *neighbor_weights,
    const float *inv_W,
    const float *inv_Wp1,
    const float *fg_gain,
    const float *bg_gain,
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
    const float *nw = neighbor_weights + idx * 4;
    const std::size_t image_idx = idx * 3;

    const PixelSolutionInputs inputs {
        .alpha = alpha[idx],
        .image0 = image[image_idx + 0],
        .image1 = image[image_idx + 1],
        .image2 = image[image_idx + 2],
        .sum_wF0 = nw[0] * foreground[idx_left * 3 + 0] + nw[1] * foreground[idx_right * 3 + 0] +
            nw[2] * foreground[idx_up * 3 + 0] + nw[3] * foreground[idx_down * 3 + 0],
        .sum_wF1 = nw[0] * foreground[idx_left * 3 + 1] + nw[1] * foreground[idx_right * 3 + 1] +
            nw[2] * foreground[idx_up * 3 + 1] + nw[3] * foreground[idx_down * 3 + 1],
        .sum_wF2 = nw[0] * foreground[idx_left * 3 + 2] + nw[1] * foreground[idx_right * 3 + 2] +
            nw[2] * foreground[idx_up * 3 + 2] + nw[3] * foreground[idx_down * 3 + 2],
        .sum_wB0 = nw[0] * background[idx_left * 3 + 0] + nw[1] * background[idx_right * 3 + 0] +
            nw[2] * background[idx_up * 3 + 0] + nw[3] * background[idx_down * 3 + 0],
        .sum_wB1 = nw[0] * background[idx_left * 3 + 1] + nw[1] * background[idx_right * 3 + 1] +
            nw[2] * background[idx_up * 3 + 1] + nw[3] * background[idx_down * 3 + 1],
        .sum_wB2 = nw[0] * background[idx_left * 3 + 2] + nw[1] * background[idx_right * 3 + 2] +
            nw[2] * background[idx_up * 3 + 2] + nw[3] * background[idx_down * 3 + 2],
        .inv_W = inv_W[idx],
        .inv_Wp1 = inv_Wp1[idx],
        .fg_gain = fg_gain[idx],
        .bg_gain = bg_gain[idx],
    };
    write_solution_raw(foreground, background, idx, inputs);
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

inline void estimate_fb_ml(
    MutableImage F_out,
    MutableImage B_out,
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
  validate_float_outputs(F_out, B_out, h0, w0);
  if (h0 <= 0 || w0 <= 0) {
    throw std::runtime_error("estimate_fb_ml: input image must be non-empty");
  }

  const float *input_image_ptr = input_image.data();
  const float *input_alpha_ptr = input_alpha.data();

  nb::gil_scoped_release release;

  const std::size_t max_pixels = static_cast<std::size_t>(h0) * static_cast<std::size_t>(w0);
  thread_local FloatWorkspace workspace;
  workspace.ensure_capacity(max_pixels);

  float fg_mean[3];
  float bg_mean[3];
  compute_initial_means_raw(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

  workspace.prevF_storage[0] = fg_mean[0];
  workspace.prevF_storage[1] = fg_mean[1];
  workspace.prevF_storage[2] = fg_mean[2];
  workspace.prevB_storage[0] = bg_mean[0];
  workspace.prevB_storage[1] = bg_mean[1];
  workspace.prevB_storage[2] = bg_mean[2];

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

    resize_nearest_multichannel_raw(workspace.image.data(), input_image_ptr, h0, w0, h, w);
    resize_nearest_raw(workspace.alpha.data(), input_alpha_ptr, h0, w0, h, w);
    build_level_coefficients_raw(
        workspace.alpha.data(),
        h,
        w,
        regularization,
        gradient_weight,
        workspace.neighbor_weights.data(),
        workspace.inv_W.data(),
        workspace.inv_Wp1.data(),
        workspace.fg_gain.data(),
        workspace.bg_gain.data());

    const bool final_level = i_level == n_levels;
    float *currF = final_level ? F_out.data() : workspace.currF_storage.data();
    float *currB = final_level ? B_out.data() : workspace.currB_storage.data();

    resize_nearest_multichannel_raw(currF, workspace.prevF_storage.data(), prev_h, prev_w, h, w);
    resize_nearest_multichannel_raw(currB, workspace.prevB_storage.data(), prev_h, prev_w, h, w);

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_rb_half_cached_raw(
          currF,
          currB,
          workspace.image.data(),
          workspace.alpha.data(),
          workspace.neighbor_weights.data(),
          workspace.inv_W.data(),
          workspace.inv_Wp1.data(),
          workspace.fg_gain.data(),
          workspace.bg_gain.data(),
          h,
          w,
          0);
      update_rb_half_cached_raw(
          currF,
          currB,
          workspace.image.data(),
          workspace.alpha.data(),
          workspace.neighbor_weights.data(),
          workspace.inv_W.data(),
          workspace.inv_Wp1.data(),
          workspace.fg_gain.data(),
          workspace.bg_gain.data(),
          h,
          w,
          1);
    }

    if (!final_level) {
      std::swap(workspace.prevF_storage, workspace.currF_storage);
      std::swap(workspace.prevB_storage, workspace.currB_storage);
      prev_h = h;
      prev_w = w;
    }
  }
}

inline void update_rb_half_cached(
    MutableImage F,
    MutableImage B,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain,
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
          .image0 = image(y, x, 0),
          .image1 = image(y, x, 1),
          .image2 = image(y, x, 2),
          .sum_wF0 = neighbor_weights(y, x, 0) * F(y, x_left, 0) + neighbor_weights(y, x, 1) * F(y, x_right, 0) +
              neighbor_weights(y, x, 2) * F(y_up, x, 0) + neighbor_weights(y, x, 3) * F(y_down, x, 0),
          .sum_wF1 = neighbor_weights(y, x, 0) * F(y, x_left, 1) + neighbor_weights(y, x, 1) * F(y, x_right, 1) +
              neighbor_weights(y, x, 2) * F(y_up, x, 1) + neighbor_weights(y, x, 3) * F(y_down, x, 1),
          .sum_wF2 = neighbor_weights(y, x, 0) * F(y, x_left, 2) + neighbor_weights(y, x, 1) * F(y, x_right, 2) +
              neighbor_weights(y, x, 2) * F(y_up, x, 2) + neighbor_weights(y, x, 3) * F(y_down, x, 2),
          .sum_wB0 = neighbor_weights(y, x, 0) * B(y, x_left, 0) + neighbor_weights(y, x, 1) * B(y, x_right, 0) +
              neighbor_weights(y, x, 2) * B(y_up, x, 0) + neighbor_weights(y, x, 3) * B(y_down, x, 0),
          .sum_wB1 = neighbor_weights(y, x, 0) * B(y, x_left, 1) + neighbor_weights(y, x, 1) * B(y, x_right, 1) +
              neighbor_weights(y, x, 2) * B(y_up, x, 1) + neighbor_weights(y, x, 3) * B(y_down, x, 1),
          .sum_wB2 = neighbor_weights(y, x, 0) * B(y, x_left, 2) + neighbor_weights(y, x, 1) * B(y, x_right, 2) +
              neighbor_weights(y, x, 2) * B(y_up, x, 2) + neighbor_weights(y, x, 3) * B(y_down, x, 2),
          .inv_W = inv_W(y, x),
          .inv_Wp1 = inv_Wp1(y, x),
          .fg_gain = fg_gain(y, x),
          .bg_gain = bg_gain(y, x),
      };
      write_solution(F, B, static_cast<std::size_t>(y), static_cast<std::size_t>(x), inputs);
    }
  }
}

inline void update_rb_half_cached_from_prev_level(
    MutableImage F,
    MutableImage B,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain,
    MutableImage F_prev,
    MutableImage B_prev,
    IndexMap x_prev_map,
    IndexMap y_prev_map,
    int h,
    int w
) {
  for (int y = 0; y < h; ++y) {
    const int x_start = y % 2;
    const std::int32_t y_current_prev = y_prev_map(y);
    const std::int32_t y_up = y == 0 ? 0 : y - 1;
    const std::int32_t y_down = y + 1 >= h ? h - 1 : y + 1;
    const std::int32_t y_up_prev = y_prev_map(y_up);
    const std::int32_t y_down_prev = y_prev_map(y_down);

    for (int x = x_start; x < w; x += 2) {
      const std::int32_t x_prev = x_prev_map(x);
      const std::int32_t x_left_prev = x_prev_map(x == 0 ? 0 : x - 1);
      const std::int32_t x_right_prev = x_prev_map(x + 1 >= w ? w - 1 : x + 1);
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;

      float sum_wF0 = 0.0f;
      float sum_wF1 = 0.0f;
      float sum_wF2 = 0.0f;
      float sum_wB0 = 0.0f;
      float sum_wB1 = 0.0f;
      float sum_wB2 = 0.0f;

      if (x_left == x) {
        sum_wF0 += neighbor_weights(y, x, 0) * F_prev(y_current_prev, x_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 0) * F_prev(y_current_prev, x_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 0) * F_prev(y_current_prev, x_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 0) * B_prev(y_current_prev, x_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 0) * B_prev(y_current_prev, x_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 0) * B_prev(y_current_prev, x_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 0) * F(y, x_left, 0);
        sum_wF1 += neighbor_weights(y, x, 0) * F(y, x_left, 1);
        sum_wF2 += neighbor_weights(y, x, 0) * F(y, x_left, 2);
        sum_wB0 += neighbor_weights(y, x, 0) * B(y, x_left, 0);
        sum_wB1 += neighbor_weights(y, x, 0) * B(y, x_left, 1);
        sum_wB2 += neighbor_weights(y, x, 0) * B(y, x_left, 2);
      }

      if (x_right == x) {
        sum_wF0 += neighbor_weights(y, x, 1) * F_prev(y_current_prev, x_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 1) * F_prev(y_current_prev, x_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 1) * F_prev(y_current_prev, x_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 1) * B_prev(y_current_prev, x_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 1) * B_prev(y_current_prev, x_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 1) * B_prev(y_current_prev, x_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 1) * F(y, x_right, 0);
        sum_wF1 += neighbor_weights(y, x, 1) * F(y, x_right, 1);
        sum_wF2 += neighbor_weights(y, x, 1) * F(y, x_right, 2);
        sum_wB0 += neighbor_weights(y, x, 1) * B(y, x_right, 0);
        sum_wB1 += neighbor_weights(y, x, 1) * B(y, x_right, 1);
        sum_wB2 += neighbor_weights(y, x, 1) * B(y, x_right, 2);
      }

      if (y_up == y) {
        sum_wF0 += neighbor_weights(y, x, 2) * F_prev(y_current_prev, x_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 2) * F_prev(y_current_prev, x_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 2) * F_prev(y_current_prev, x_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 2) * B_prev(y_current_prev, x_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 2) * B_prev(y_current_prev, x_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 2) * B_prev(y_current_prev, x_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 2) * F(y_up, x, 0);
        sum_wF1 += neighbor_weights(y, x, 2) * F(y_up, x, 1);
        sum_wF2 += neighbor_weights(y, x, 2) * F(y_up, x, 2);
        sum_wB0 += neighbor_weights(y, x, 2) * B(y_up, x, 0);
        sum_wB1 += neighbor_weights(y, x, 2) * B(y_up, x, 1);
        sum_wB2 += neighbor_weights(y, x, 2) * B(y_up, x, 2);
      }

      if (y_down == y) {
        sum_wF0 += neighbor_weights(y, x, 3) * F_prev(y_current_prev, x_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 3) * F_prev(y_current_prev, x_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 3) * F_prev(y_current_prev, x_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 3) * B_prev(y_current_prev, x_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 3) * B_prev(y_current_prev, x_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 3) * B_prev(y_current_prev, x_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 3) * F(y_down, x, 0);
        sum_wF1 += neighbor_weights(y, x, 3) * F(y_down, x, 1);
        sum_wF2 += neighbor_weights(y, x, 3) * F(y_down, x, 2);
        sum_wB0 += neighbor_weights(y, x, 3) * B(y_down, x, 0);
        sum_wB1 += neighbor_weights(y, x, 3) * B(y_down, x, 1);
        sum_wB2 += neighbor_weights(y, x, 3) * B(y_down, x, 2);
      }

      const PixelSolutionInputs inputs {
          .alpha = alpha(y, x),
          .image0 = image(y, x, 0),
          .image1 = image(y, x, 1),
          .image2 = image(y, x, 2),
          .sum_wF0 = sum_wF0,
          .sum_wF1 = sum_wF1,
          .sum_wF2 = sum_wF2,
          .sum_wB0 = sum_wB0,
          .sum_wB1 = sum_wB1,
          .sum_wB2 = sum_wB2,
          .inv_W = inv_W(y, x),
          .inv_Wp1 = inv_Wp1(y, x),
          .fg_gain = fg_gain(y, x),
          .bg_gain = bg_gain(y, x),
      };
      write_solution(F, B, static_cast<std::size_t>(y), static_cast<std::size_t>(x), inputs);
    }
  }
}

inline void update_rb_half_cached_from_prev_level_with_boundary_fallback(
    MutableImage F,
    MutableImage B,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain,
    MutableImage F_prev,
    MutableImage B_prev,
    IndexMap x_prev_map,
    IndexMap y_prev_map,
    int h,
    int w
) {
  for (int y = 0; y < h; ++y) {
    const int x_start = (1 + y) % 2;
    const std::int32_t y_current_prev = y_prev_map(y);
    const std::int32_t y_up = y == 0 ? 0 : y - 1;
    const std::int32_t y_down = y + 1 >= h ? h - 1 : y + 1;
    const std::int32_t y_up_prev = y_prev_map(y_up);
    const std::int32_t y_down_prev = y_prev_map(y_down);

    for (int x = x_start; x < w; x += 2) {
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;
      const std::int32_t x_current_prev = x_prev_map(x);

      float sum_wF0 = 0.0f;
      float sum_wF1 = 0.0f;
      float sum_wF2 = 0.0f;
      float sum_wB0 = 0.0f;
      float sum_wB1 = 0.0f;
      float sum_wB2 = 0.0f;

      if (x_left == x) {
        sum_wF0 += neighbor_weights(y, x, 0) * F_prev(y_current_prev, x_current_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 0) * F_prev(y_current_prev, x_current_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 0) * F_prev(y_current_prev, x_current_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 0) * B_prev(y_current_prev, x_current_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 0) * B_prev(y_current_prev, x_current_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 0) * B_prev(y_current_prev, x_current_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 0) * F(y, x_left, 0);
        sum_wF1 += neighbor_weights(y, x, 0) * F(y, x_left, 1);
        sum_wF2 += neighbor_weights(y, x, 0) * F(y, x_left, 2);
        sum_wB0 += neighbor_weights(y, x, 0) * B(y, x_left, 0);
        sum_wB1 += neighbor_weights(y, x, 0) * B(y, x_left, 1);
        sum_wB2 += neighbor_weights(y, x, 0) * B(y, x_left, 2);
      }

      if (x_right == x) {
        sum_wF0 += neighbor_weights(y, x, 1) * F_prev(y_current_prev, x_current_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 1) * F_prev(y_current_prev, x_current_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 1) * F_prev(y_current_prev, x_current_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 1) * B_prev(y_current_prev, x_current_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 1) * B_prev(y_current_prev, x_current_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 1) * B_prev(y_current_prev, x_current_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 1) * F(y, x_right, 0);
        sum_wF1 += neighbor_weights(y, x, 1) * F(y, x_right, 1);
        sum_wF2 += neighbor_weights(y, x, 1) * F(y, x_right, 2);
        sum_wB0 += neighbor_weights(y, x, 1) * B(y, x_right, 0);
        sum_wB1 += neighbor_weights(y, x, 1) * B(y, x_right, 1);
        sum_wB2 += neighbor_weights(y, x, 1) * B(y, x_right, 2);
      }

      if (y_up == y) {
        sum_wF0 += neighbor_weights(y, x, 2) * F_prev(y_current_prev, x_current_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 2) * F_prev(y_current_prev, x_current_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 2) * F_prev(y_current_prev, x_current_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 2) * B_prev(y_current_prev, x_current_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 2) * B_prev(y_current_prev, x_current_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 2) * B_prev(y_current_prev, x_current_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 2) * F(y_up, x, 0);
        sum_wF1 += neighbor_weights(y, x, 2) * F(y_up, x, 1);
        sum_wF2 += neighbor_weights(y, x, 2) * F(y_up, x, 2);
        sum_wB0 += neighbor_weights(y, x, 2) * B(y_up, x, 0);
        sum_wB1 += neighbor_weights(y, x, 2) * B(y_up, x, 1);
        sum_wB2 += neighbor_weights(y, x, 2) * B(y_up, x, 2);
      }

      if (y_down == y) {
        sum_wF0 += neighbor_weights(y, x, 3) * F_prev(y_current_prev, x_current_prev, 0);
        sum_wF1 += neighbor_weights(y, x, 3) * F_prev(y_current_prev, x_current_prev, 1);
        sum_wF2 += neighbor_weights(y, x, 3) * F_prev(y_current_prev, x_current_prev, 2);
        sum_wB0 += neighbor_weights(y, x, 3) * B_prev(y_current_prev, x_current_prev, 0);
        sum_wB1 += neighbor_weights(y, x, 3) * B_prev(y_current_prev, x_current_prev, 1);
        sum_wB2 += neighbor_weights(y, x, 3) * B_prev(y_current_prev, x_current_prev, 2);
      } else {
        sum_wF0 += neighbor_weights(y, x, 3) * F(y_down, x, 0);
        sum_wF1 += neighbor_weights(y, x, 3) * F(y_down, x, 1);
        sum_wF2 += neighbor_weights(y, x, 3) * F(y_down, x, 2);
        sum_wB0 += neighbor_weights(y, x, 3) * B(y_down, x, 0);
        sum_wB1 += neighbor_weights(y, x, 3) * B(y_down, x, 1);
        sum_wB2 += neighbor_weights(y, x, 3) * B(y_down, x, 2);
      }

      const PixelSolutionInputs inputs {
          .alpha = alpha(y, x),
          .image0 = image(y, x, 0),
          .image1 = image(y, x, 1),
          .image2 = image(y, x, 2),
          .sum_wF0 = sum_wF0,
          .sum_wF1 = sum_wF1,
          .sum_wF2 = sum_wF2,
          .sum_wB0 = sum_wB0,
          .sum_wB1 = sum_wB1,
          .sum_wB2 = sum_wB2,
          .inv_W = inv_W(y, x),
          .inv_Wp1 = inv_Wp1(y, x),
          .fg_gain = fg_gain(y, x),
          .bg_gain = bg_gain(y, x),
      };
      write_solution(F, B, static_cast<std::size_t>(y), static_cast<std::size_t>(x), inputs);
    }
  }
}

}  // namespace
