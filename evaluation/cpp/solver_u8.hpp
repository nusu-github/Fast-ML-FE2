#pragma once

#include "common.hpp"
#include "resize_ops.hpp"

namespace {

inline void compute_initial_means_u8_raw(
    const std::uint8_t *image,
    const std::uint8_t *alpha,
    int h,
    int w,
    std::uint8_t fg_mean[3],
    std::uint8_t bg_mean[3]
) {
  double fg_sum[3] {0.0, 0.0, 0.0};
  double bg_sum[3] {0.0, 0.0, 0.0};
  int fg_count = 0;
  int bg_count = 0;

  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x) {
      const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
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
    fg_mean[c] = fg_count > 0 ? static_cast<std::uint8_t>(std::clamp<int>(
                                     static_cast<int>(std::lround(fg_sum[c] / fg_count)),
                                     0,
                                     255))
                              : static_cast<std::uint8_t>(0);
    bg_mean[c] = bg_count > 0 ? static_cast<std::uint8_t>(std::clamp<int>(
                                     static_cast<int>(std::lround(bg_sum[c] / bg_count)),
                                     0,
                                     255))
                              : static_cast<std::uint8_t>(0);
  }
}

inline void build_level_coefficients_u8_raw(
    const std::uint8_t *alpha,
    int h,
    int w,
    const std::uint32_t *weight_lut,
    float weight_scale_inv,
    const float *u8_to_f32,
    float *neighbor_weights,
    float *inv_W,
    float *inv_Wp1,
    float *fg_gain,
    float *bg_gain
) {
  if (h <= 0 || w <= 0) {
    return;
  }

  auto lookup_weight = [&](std::uint8_t a0, std::uint8_t a1) {
    return static_cast<float>(weight_lut[static_cast<std::size_t>(a0) * 256 + a1]) * weight_scale_inv;
  };

  auto process_interior_pixel = [&](int y, int x) {
    const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::uint8_t a0 = alpha[idx];
    const float a0_f = u8_to_f32[a0];
    const float a1_f = 1.0f - a0_f;

    const float w0 = lookup_weight(a0, alpha[idx - 1]);
    const float w1 = lookup_weight(a0, alpha[idx + 1]);
    const float w2 = lookup_weight(a0, alpha[idx - static_cast<std::size_t>(w)]);
    const float w3 = lookup_weight(a0, alpha[idx + static_cast<std::size_t>(w)]);

    float *nw = neighbor_weights + idx * 4;
    nw[0] = w0;
    nw[1] = w1;
    nw[2] = w2;
    nw[3] = w3;

    const float W = w0 + w1 + w2 + w3;
    inv_W[idx] = 1.0f / W;
    inv_Wp1[idx] = 1.0f / (W + 1.0f);

    const float D = W + a0_f * a0_f + a1_f * a1_f;
    const float inv_D = 1.0f / D;
    fg_gain[idx] = a0_f * inv_D;
    bg_gain[idx] = a1_f * inv_D;
  };

  auto process_boundary_pixel = [&](int y, int x) {
    const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::uint8_t a0 = alpha[idx];
    const float a0_f = u8_to_f32[a0];
    const float a1_f = 1.0f - a0_f;

    const int x_left = x == 0 ? 0 : x - 1;
    const int x_right = std::min(w - 1, x + 1);
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = std::min(h - 1, y + 1);

    const float w0 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w))]);
    const float w1 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w))]);
    const float w2 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);
    const float w3 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);

    float *nw = neighbor_weights + idx * 4;
    nw[0] = w0;
    nw[1] = w1;
    nw[2] = w2;
    nw[3] = w3;

    const float W = w0 + w1 + w2 + w3;
    inv_W[idx] = 1.0f / W;
    inv_Wp1[idx] = 1.0f / (W + 1.0f);

    const float D = W + a0_f * a0_f + a1_f * a1_f;
    const float inv_D = 1.0f / D;
    fg_gain[idx] = a0_f * inv_D;
    bg_gain[idx] = a1_f * inv_D;
  };

  if (h > 2 && w > 2) {
    for (int y = 1; y < h - 1; ++y) {
      for (int x = 1; x < w - 1; ++x) {
        process_interior_pixel(y, x);
      }
    }
  }

  for (int x = 0; x < w; ++x) {
    process_boundary_pixel(0, x);
  }

  if (h > 1) {
    for (int x = 0; x < w; ++x) {
      process_boundary_pixel(h - 1, x);
    }
  }

  for (int y = 1; y < h - 1; ++y) {
    process_boundary_pixel(y, 0);
    if (w > 1) {
      process_boundary_pixel(y, w - 1);
    }
  }
}

inline void write_solution_u8(std::uint8_t *foreground, std::uint8_t *background, std::size_t idx, const PixelSolutionInputs &inputs) {
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

  std::uint8_t *F_px = foreground + idx * 3;
  std::uint8_t *B_px = background + idx * 3;

  if (inputs.alpha < 0.01f) {
    F_px[0] = quantize01_to_u8(mu_F0);
    F_px[1] = quantize01_to_u8(mu_F1);
    F_px[2] = quantize01_to_u8(mu_F2);
    B_px[0] = quantize01_to_u8(mu_B0 + r0 * inputs.inv_Wp1);
    B_px[1] = quantize01_to_u8(mu_B1 + r1 * inputs.inv_Wp1);
    B_px[2] = quantize01_to_u8(mu_B2 + r2 * inputs.inv_Wp1);
  } else if (inputs.alpha > 0.99f) {
    F_px[0] = quantize01_to_u8(mu_F0 + r0 * inputs.inv_Wp1);
    F_px[1] = quantize01_to_u8(mu_F1 + r1 * inputs.inv_Wp1);
    F_px[2] = quantize01_to_u8(mu_F2 + r2 * inputs.inv_Wp1);
    B_px[0] = quantize01_to_u8(mu_B0);
    B_px[1] = quantize01_to_u8(mu_B1);
    B_px[2] = quantize01_to_u8(mu_B2);
  } else {
    F_px[0] = quantize01_to_u8(mu_F0 + inputs.fg_gain * r0);
    F_px[1] = quantize01_to_u8(mu_F1 + inputs.fg_gain * r1);
    F_px[2] = quantize01_to_u8(mu_F2 + inputs.fg_gain * r2);
    B_px[0] = quantize01_to_u8(mu_B0 + inputs.bg_gain * r0);
    B_px[1] = quantize01_to_u8(mu_B1 + inputs.bg_gain * r1);
    B_px[2] = quantize01_to_u8(mu_B2 + inputs.bg_gain * r2);
  }
}

inline void update_rb_half_cached_u8_raw(
    std::uint8_t *foreground,
    std::uint8_t *background,
    const std::uint8_t *image,
    const std::uint8_t *alpha,
    const float *u8_to_f32,
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
    const float alpha0 = u8_to_f32[alpha[idx]];
    const int x_left = x == 0 ? 0 : x - 1;
    const int x_right = x + 1 >= w ? w - 1 : x + 1;
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = y + 1 >= h ? h - 1 : y + 1;

    const std::size_t idx_left = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w));
    const std::size_t idx_right = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w));
    const std::size_t idx_up = scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::size_t idx_down = scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w));

    const float w0 = neighbor_weights[idx * 4 + 0];
    const float w1 = neighbor_weights[idx * 4 + 1];
    const float w2 = neighbor_weights[idx * 4 + 2];
    const float w3 = neighbor_weights[idx * 4 + 3];

    const float sum_wF0 =
        w0 * u8_to_f32[foreground[idx_left * 3 + 0]] + w1 * u8_to_f32[foreground[idx_right * 3 + 0]] +
        w2 * u8_to_f32[foreground[idx_up * 3 + 0]] + w3 * u8_to_f32[foreground[idx_down * 3 + 0]];
    const float sum_wF1 =
        w0 * u8_to_f32[foreground[idx_left * 3 + 1]] + w1 * u8_to_f32[foreground[idx_right * 3 + 1]] +
        w2 * u8_to_f32[foreground[idx_up * 3 + 1]] + w3 * u8_to_f32[foreground[idx_down * 3 + 1]];
    const float sum_wF2 =
        w0 * u8_to_f32[foreground[idx_left * 3 + 2]] + w1 * u8_to_f32[foreground[idx_right * 3 + 2]] +
        w2 * u8_to_f32[foreground[idx_up * 3 + 2]] + w3 * u8_to_f32[foreground[idx_down * 3 + 2]];
    const float sum_wB0 =
        w0 * u8_to_f32[background[idx_left * 3 + 0]] + w1 * u8_to_f32[background[idx_right * 3 + 0]] +
        w2 * u8_to_f32[background[idx_up * 3 + 0]] + w3 * u8_to_f32[background[idx_down * 3 + 0]];
    const float sum_wB1 =
        w0 * u8_to_f32[background[idx_left * 3 + 1]] + w1 * u8_to_f32[background[idx_right * 3 + 1]] +
        w2 * u8_to_f32[background[idx_up * 3 + 1]] + w3 * u8_to_f32[background[idx_down * 3 + 1]];
    const float sum_wB2 =
        w0 * u8_to_f32[background[idx_left * 3 + 2]] + w1 * u8_to_f32[background[idx_right * 3 + 2]] +
        w2 * u8_to_f32[background[idx_up * 3 + 2]] + w3 * u8_to_f32[background[idx_down * 3 + 2]];

    const std::size_t image_idx = idx * 3;
    const PixelSolutionInputs inputs {
        .alpha = alpha0,
        .image0 = u8_to_f32[image[image_idx + 0]],
        .image1 = u8_to_f32[image[image_idx + 1]],
        .image2 = u8_to_f32[image[image_idx + 2]],
        .sum_wF0 = sum_wF0,
        .sum_wF1 = sum_wF1,
        .sum_wF2 = sum_wF2,
        .sum_wB0 = sum_wB0,
        .sum_wB1 = sum_wB1,
        .sum_wB2 = sum_wB2,
        .inv_W = inv_W[idx],
        .inv_Wp1 = inv_Wp1[idx],
        .fg_gain = fg_gain[idx],
        .bg_gain = bg_gain[idx],
    };
    write_solution_u8(foreground, background, idx, inputs);
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

inline void estimate_fb_ml_u8(
    MutableImageU8 F_out,
    MutableImageU8 B_out,
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
  validate_u8_outputs(F_out, B_out, h0, w0);
  if (h0 <= 0 || w0 <= 0) {
    throw std::runtime_error("estimate_fb_ml_u8: input image must be non-empty");
  }

  const auto *input_image_ptr = input_image.data();
  const auto *input_alpha_ptr = input_alpha.data();

  nb::gil_scoped_release release;

  const std::size_t max_pixels = static_cast<std::size_t>(h0) * static_cast<std::size_t>(w0);
  thread_local U8Workspace workspace;
  workspace.ensure_capacity(max_pixels);

  constexpr float weight_scale = 65536.0f;
  constexpr float weight_scale_inv = 1.0f / weight_scale;
  constexpr float inv256 = 1.0f / 256.0f;

  if (workspace.needs_weight_lut_refresh(regularization, gradient_weight)) {
    for (int a0 = 0; a0 < 256; ++a0) {
      for (int a1 = 0; a1 < 256; ++a1) {
        const std::uint32_t diff_q8 = div255_fast(static_cast<std::uint32_t>(std::abs(a0 - a1)) * 256u);
        const float diff = static_cast<float>(diff_q8) * inv256;
        const double scaled = static_cast<double>(regularization + gradient_weight * diff) * weight_scale;
        const double clamped =
            std::max(0.0, std::min(scaled, static_cast<double>(std::numeric_limits<std::uint32_t>::max())));
        workspace.weight_lut[static_cast<std::size_t>(a0) * 256 + a1] = static_cast<std::uint32_t>(std::lround(clamped));
      }
    }
    workspace.mark_weight_lut_ready(regularization, gradient_weight);
  }

  std::uint8_t fg_mean[3];
  std::uint8_t bg_mean[3];
  compute_initial_means_u8_raw(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

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

    workspace.x_map.resize(w);
    workspace.y_map.resize(h);
    build_resize_index_map_raw(w0, workspace.x_map);
    build_resize_index_map_raw(h0, workspace.y_map);
    resize_nearest_multichannel_u8_raw(
        workspace.image.data(),
        input_image_ptr,
        workspace.x_map.data(),
        workspace.y_map.data(),
        w0,
        h,
        w);
    resize_nearest_u8_raw(
        workspace.alpha.data(),
        input_alpha_ptr,
        workspace.x_map.data(),
        workspace.y_map.data(),
        w0,
        h,
        w);
    build_level_coefficients_u8_raw(
        workspace.alpha.data(),
        h,
        w,
        workspace.weight_lut.data(),
        weight_scale_inv,
        workspace.u8_to_f32.data(),
        workspace.neighbor_weights.data(),
        workspace.inv_W.data(),
        workspace.inv_Wp1.data(),
        workspace.fg_gain.data(),
        workspace.bg_gain.data());

    const bool final_level = i_level == n_levels;
    std::uint8_t *currF = final_level ? F_out.data() : workspace.currF_storage.data();
    std::uint8_t *currB = final_level ? B_out.data() : workspace.currB_storage.data();

    workspace.prev_x_map.resize(w);
    workspace.prev_y_map.resize(h);
    build_resize_index_map_raw(prev_w, workspace.prev_x_map);
    build_resize_index_map_raw(prev_h, workspace.prev_y_map);

    resize_nearest_multichannel_u8_raw(
        currF,
        workspace.prevF_storage.data(),
        workspace.prev_x_map.data(),
        workspace.prev_y_map.data(),
        prev_w,
        h,
        w);
    resize_nearest_multichannel_u8_raw(
        currB,
        workspace.prevB_storage.data(),
        workspace.prev_x_map.data(),
        workspace.prev_y_map.data(),
        prev_w,
        h,
        w);

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_rb_half_cached_u8_raw(
          currF,
          currB,
          workspace.image.data(),
          workspace.alpha.data(),
          workspace.u8_to_f32.data(),
          workspace.neighbor_weights.data(),
          workspace.inv_W.data(),
          workspace.inv_Wp1.data(),
          workspace.fg_gain.data(),
          workspace.bg_gain.data(),
          h,
          w,
          0);
      update_rb_half_cached_u8_raw(
          currF,
          currB,
          workspace.image.data(),
          workspace.alpha.data(),
          workspace.u8_to_f32.data(),
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

}  // namespace
