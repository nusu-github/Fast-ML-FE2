#pragma once

#include "aos_workspace.hpp"
#include "common.hpp"
#include "resize_ops.hpp"

namespace {

inline float fmadd(float a, float b, float c) {
  return std::fmaf(a, b, c);
}

inline PixelSolutionInputs make_pixel_solution_inputs(
    float alpha,
    const float *image_px,
    const float *foreground_weighted_sum,
    const float *background_weighted_sum,
    float inverse_weight_sum,
    float inverse_weight_sum_plus_one,
    float foreground_gain,
    float background_gain
) {
  return PixelSolutionInputs {
      .alpha = alpha,
      .image_r = image_px[0],
      .image_g = image_px[1],
      .image_b = image_px[2],
      .foreground_weighted_sum_r = foreground_weighted_sum[0],
      .foreground_weighted_sum_g = foreground_weighted_sum[1],
      .foreground_weighted_sum_b = foreground_weighted_sum[2],
      .background_weighted_sum_r = background_weighted_sum[0],
      .background_weighted_sum_g = background_weighted_sum[1],
      .background_weighted_sum_b = background_weighted_sum[2],
      .inverse_weight_sum = inverse_weight_sum,
      .inverse_weight_sum_plus_one = inverse_weight_sum_plus_one,
      .foreground_gain = foreground_gain,
      .background_gain = background_gain,
  };
}

template <AlphaRegion Region, typename WritePixel>
inline void write_solution_channels(const PixelSolutionInputs &inputs, WritePixel &&write_pixel) {
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

  const float mu_F[kChannels] {mu_F0, mu_F1, mu_F2};
  const float mu_B[kChannels] {mu_B0, mu_B1, mu_B2};
  const float residual[kChannels] {r0, r1, r2};

  apply_rgb([&]<std::size_t C>(std::integral_constant<std::size_t, C>) {
    if constexpr (Region == AlphaRegion::low) {
      write_pixel(true, C, clamp01(mu_F[C]));
      write_pixel(false, C, clamp01(fmadd(inputs.inverse_weight_sum_plus_one, residual[C], mu_B[C])));
    } else if constexpr (Region == AlphaRegion::high) {
      write_pixel(true, C, clamp01(fmadd(inputs.inverse_weight_sum_plus_one, residual[C], mu_F[C])));
      write_pixel(false, C, clamp01(mu_B[C]));
    } else {
      write_pixel(true, C, clamp01(fmadd(inputs.foreground_gain, residual[C], mu_F[C])));
      write_pixel(false, C, clamp01(fmadd(inputs.background_gain, residual[C], mu_B[C])));
    }
  });
}

inline auto build_multilevel_shapes_flat(int h0, int w0, int small_size, int n_small_iterations, int n_big_iterations)
    -> std::vector<std::int32_t> {
  const int max_dim = std::max(h0, w0);
  const int n_levels = ceil_log2_int(max_dim);
  std::vector<std::int32_t> flat_shapes(static_cast<std::size_t>(n_levels + 1) * 3);

  for (int i_level = 0; i_level <= n_levels; ++i_level) {
    int h;
    int w;
    int n_iter;

    if (max_dim <= 1) {
      h = 1;
      w = 1;
      n_iter = n_small_iterations;
    } else {
      const double ratio = static_cast<double>(i_level) / static_cast<double>(n_levels);
      w = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(w0), ratio)));
      h = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(h0), ratio)));
      n_iter = (w <= small_size && h <= small_size) ? n_small_iterations : n_big_iterations;
    }

    const std::size_t base = static_cast<std::size_t>(i_level) * 3;
    flat_shapes[base + 0] = h;
    flat_shapes[base + 1] = w;
    flat_shapes[base + 2] = n_iter;
  }

  return flat_shapes;
}

inline void write_solution(
    MutableImage foreground,
    MutableImage background,
    std::size_t y,
    std::size_t x,
    const PixelSolutionInputs &inputs
) {
  switch (classify_alpha_region(inputs.alpha)) {
    case AlphaRegion::low:
      write_solution_channels<AlphaRegion::low>(inputs, [&](bool is_foreground, std::size_t c, float value) {
        (is_foreground ? foreground : background)(y, x, c) = value;
      });
      break;
    case AlphaRegion::high:
      write_solution_channels<AlphaRegion::high>(inputs, [&](bool is_foreground, std::size_t c, float value) {
        (is_foreground ? foreground : background)(y, x, c) = value;
      });
      break;
    case AlphaRegion::middle:
      write_solution_channels<AlphaRegion::middle>(inputs, [&](bool is_foreground, std::size_t c, float value) {
        (is_foreground ? foreground : background)(y, x, c) = value;
      });
      break;
  }
}

inline void write_solution_buffer(float *foreground, float *background, std::size_t idx, const PixelSolutionInputs &inputs) {
  float *foreground_px = foreground + rgb_pixel_base(idx);
  float *background_px = background + rgb_pixel_base(idx);

  switch (classify_alpha_region(inputs.alpha)) {
    case AlphaRegion::low:
      write_solution_channels<AlphaRegion::low>(inputs, [&](bool is_foreground, std::size_t c, float value) {
        (is_foreground ? foreground_px : background_px)[c] = value;
      });
      break;
    case AlphaRegion::high:
      write_solution_channels<AlphaRegion::high>(inputs, [&](bool is_foreground, std::size_t c, float value) {
        (is_foreground ? foreground_px : background_px)[c] = value;
      });
      break;
    case AlphaRegion::middle:
      write_solution_channels<AlphaRegion::middle>(inputs, [&](bool is_foreground, std::size_t c, float value) {
        (is_foreground ? foreground_px : background_px)[c] = value;
      });
      break;
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
        apply_rgb([&]<std::size_t C>(std::integral_constant<std::size_t, C>) {
          fg_sum[C] += px[C];
        });
        ++fg_count;
      }
      if (alpha0 < kInitialBackgroundThreshold) {
        apply_rgb([&]<std::size_t C>(std::integral_constant<std::size_t, C>) {
          bg_sum[C] += px[C];
        });
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
);

template <bool InteriorOnly>
inline void build_level_solver_coefficients_region_buffer(
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
    const std::size_t idx_left =
        InteriorOnly ? idx - 1 : scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x == 0 ? 0 : x - 1), static_cast<std::size_t>(w));
    const std::size_t idx_right =
        InteriorOnly ? idx + 1 : scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(std::min(w - 1, x + 1)), static_cast<std::size_t>(w));
    const std::size_t idx_up =
        InteriorOnly ? idx - static_cast<std::size_t>(w)
                     : scalar_index(static_cast<std::size_t>(y == 0 ? 0 : y - 1), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::size_t idx_down =
        InteriorOnly ? idx + static_cast<std::size_t>(w)
                     : scalar_index(static_cast<std::size_t>(std::min(h - 1, y + 1)), static_cast<std::size_t>(x), static_cast<std::size_t>(w));

    const float w0 = regularization + gradient_weight * std::fabs(alpha0 - alpha[idx_left]);
    const float w1 = regularization + gradient_weight * std::fabs(alpha0 - alpha[idx_right]);
    const float w2 = regularization + gradient_weight * std::fabs(alpha0 - alpha[idx_up]);
    const float w3 = regularization + gradient_weight * std::fabs(alpha0 - alpha[idx_down]);

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

  if constexpr (InteriorOnly) {
    if (h <= 2 || w <= 2) {
      return;
    }
    for (int y = 1; y < h - 1; ++y) {
      for (int x = 1; x < w - 1; ++x) {
        process_pixel(y, x);
      }
    }
  } else {
    for (int y = 0; y < h; ++y) {
      if (y != 0 && y + 1 < h) {
        continue;
      }
      for (int x = 0; x < w; ++x) {
        process_pixel(y, x);
      }
    }

    for (int y = 1; y < h - 1; ++y) {
      process_pixel(y, 0);
      if (w > 1) {
        process_pixel(y, w - 1);
      }
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
  build_level_solver_coefficients_region_buffer<true>(
      alpha,
      h,
      w,
      regularization,
      gradient_weight,
      neighbor_weights,
      inverse_weight_sum,
      inverse_weight_sum_plus_one,
      foreground_gain,
      background_gain);
  build_level_solver_coefficients_region_buffer<false>(
      alpha,
      h,
      w,
      regularization,
      gradient_weight,
      neighbor_weights,
      inverse_weight_sum,
      inverse_weight_sum_plus_one,
      foreground_gain,
      background_gain);
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
);

template <bool InteriorOnly>
inline void update_red_black_half_step_region_buffer(
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

  const SweepColor sweep_color = static_cast<SweepColor>(color);

  auto process_pixel = [&](int y, int x) {
    const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const int x_left = InteriorOnly ? x - 1 : (x == 0 ? 0 : x - 1);
    const int x_right = InteriorOnly ? x + 1 : (x + 1 >= w ? w - 1 : x + 1);
    const int y_up = InteriorOnly ? y - 1 : (y == 0 ? 0 : y - 1);
    const int y_down = InteriorOnly ? y + 1 : (y + 1 >= h ? h - 1 : y + 1);
    const std::size_t idx_left = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w));
    const std::size_t idx_right = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w));
    const std::size_t idx_up = scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const std::size_t idx_down = scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
    const float *nw = neighbor_weights + idx * kNeighborCount;
    const std::size_t image_idx = rgb_pixel_base(idx);
    float foreground_weighted_sum[kChannels] {};
    float background_weighted_sum[kChannels] {};

    apply_rgb([&]<std::size_t C>(std::integral_constant<std::size_t, C>) {
      foreground_weighted_sum[C] =
          nw[0] * foreground[rgb_pixel_base(idx_left) + C] + nw[1] * foreground[rgb_pixel_base(idx_right) + C] +
          nw[2] * foreground[rgb_pixel_base(idx_up) + C] + nw[3] * foreground[rgb_pixel_base(idx_down) + C];
      background_weighted_sum[C] =
          nw[0] * background[rgb_pixel_base(idx_left) + C] + nw[1] * background[rgb_pixel_base(idx_right) + C] +
          nw[2] * background[rgb_pixel_base(idx_up) + C] + nw[3] * background[rgb_pixel_base(idx_down) + C];
    });

    const PixelSolutionInputs inputs = make_pixel_solution_inputs(
        alpha[idx],
        image + image_idx,
        foreground_weighted_sum,
        background_weighted_sum,
        inverse_weight_sum[idx],
        inverse_weight_sum_plus_one[idx],
        foreground_gain[idx],
        background_gain[idx]);
    write_solution_buffer(foreground, background, idx, inputs);
  };

  if constexpr (InteriorOnly) {
    if (h <= 2 || w <= 2) {
      return;
    }
    for (int y = 1; y < h - 1; ++y) {
      const int x_start = interior_x_start(y, sweep_color);
      for (int x = x_start; x < w - 1; x += 2) {
        process_pixel(y, x);
      }
    }
  } else {
    for (int y = 0; y < h; ++y) {
      if (y != 0 && y + 1 < h) {
        continue;
      }
      const int x_start = parity_of(y, sweep_color);
      for (int x = x_start; x < w; x += 2) {
        process_pixel(y, x);
      }
    }

    for (int y = 1; y < h - 1; ++y) {
      if (parity_of(y, sweep_color) == 0) {
        process_pixel(y, 0);
      }
      if (w > 1 && parity_of(y + w - 1, sweep_color) == 0) {
        process_pixel(y, w - 1);
      }
    }
  }
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
  update_red_black_half_step_region_buffer<true>(
      foreground,
      background,
      image,
      alpha,
      neighbor_weights,
      inverse_weight_sum,
      inverse_weight_sum_plus_one,
      foreground_gain,
      background_gain,
      h,
      w,
      color);
  update_red_black_half_step_region_buffer<false>(
      foreground,
      background,
      image,
      alpha,
      neighbor_weights,
      inverse_weight_sum,
      inverse_weight_sum_plus_one,
      foreground_gain,
      background_gain,
      h,
      w,
      color);
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
  workspace.ensure_pixel_capacity(max_pixels);

  float fg_mean[kChannels] {};
  float bg_mean[kChannels] {};
  compute_initial_means_buffer(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

  workspace.state.previous_foreground[0] = fg_mean[0];
  workspace.state.previous_foreground[1] = fg_mean[1];
  workspace.state.previous_foreground[2] = fg_mean[2];
  workspace.state.previous_background[0] = bg_mean[0];
  workspace.state.previous_background[1] = bg_mean[1];
  workspace.state.previous_background[2] = bg_mean[2];

  int prev_h = 1;
  int prev_w = 1;
  const auto level_shapes = build_multilevel_shapes_flat(h0, w0, small_size, n_small_iterations, n_big_iterations);
  const int n_levels = static_cast<int>(level_shapes.size() / 3) - 1;

  for (int i_level = 0; i_level <= n_levels; ++i_level) {
    const std::size_t shape_base = static_cast<std::size_t>(i_level) * 3;
    const int h = level_shapes[shape_base + 0];
    const int w = level_shapes[shape_base + 1];
    const int n_iter = level_shapes[shape_base + 2];

    resize_nearest_rgb_buffer(workspace.input.image.data(), input_image_ptr, h0, w0, h, w);
    resize_nearest_scalar_buffer(workspace.input.alpha.data(), input_alpha_ptr, h0, w0, h, w);
    build_level_solver_coefficients_buffer(
        workspace.input.alpha.data(),
        h,
        w,
        regularization,
        gradient_weight,
        workspace.coeff.neighbor_weights.data(),
        workspace.coeff.inverse_weight_sum.data(),
        workspace.coeff.inverse_weight_sum_plus_one.data(),
        workspace.coeff.foreground_gain.data(),
        workspace.coeff.background_gain.data());

    const bool final_level = i_level == n_levels;
    float *current_foreground = final_level ? foreground_out.data() : workspace.state.current_foreground.data();
    float *current_background = final_level ? background_out.data() : workspace.state.current_background.data();

    resize_nearest_rgb_buffer(current_foreground, workspace.state.previous_foreground.data(), prev_h, prev_w, h, w);
    resize_nearest_rgb_buffer(current_background, workspace.state.previous_background.data(), prev_h, prev_w, h, w);

    for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
      update_red_black_half_step_buffer(
          current_foreground,
          current_background,
          workspace.input.image.data(),
          workspace.input.alpha.data(),
          workspace.coeff.neighbor_weights.data(),
          workspace.coeff.inverse_weight_sum.data(),
          workspace.coeff.inverse_weight_sum_plus_one.data(),
          workspace.coeff.foreground_gain.data(),
          workspace.coeff.background_gain.data(),
          h,
          w,
          static_cast<int>(SweepColor::red));
      update_red_black_half_step_buffer(
          current_foreground,
          current_background,
          workspace.input.image.data(),
          workspace.input.alpha.data(),
          workspace.coeff.neighbor_weights.data(),
          workspace.coeff.inverse_weight_sum.data(),
          workspace.coeff.inverse_weight_sum_plus_one.data(),
          workspace.coeff.foreground_gain.data(),
          workspace.coeff.background_gain.data(),
          h,
          w,
          static_cast<int>(SweepColor::black));
    }

    if (!final_level) {
      std::swap(workspace.state.previous_foreground, workspace.state.current_foreground);
      std::swap(workspace.state.previous_background, workspace.state.current_background);
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
);

template <bool BoundaryFallback>
inline void update_red_black_half_step_from_previous_level_buffer(
    float *foreground,
    float *background,
    const float *image,
    const float *alpha,
    const float *neighbor_weights,
    const float *inverse_weight_sum,
    const float *inverse_weight_sum_plus_one,
    const float *foreground_gain,
    const float *background_gain,
    const float *previous_foreground,
    const float *previous_background,
    const std::int32_t *x_previous_index_map,
    const std::int32_t *y_previous_index_map,
    int h,
    int w,
    int previous_width
) {
  const SweepColor sweep_color = BoundaryFallback ? SweepColor::black : SweepColor::red;

  for (int y = 0; y < h; ++y) {
    const int x_start = parity_of(y, sweep_color);
    const std::int32_t y_current_prev = y_previous_index_map[y];
    const int y_up = y == 0 ? 0 : y - 1;
    const int y_down = y + 1 >= h ? h - 1 : y + 1;

    for (int x = x_start; x < w; x += 2) {
      const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
      const int x_left = x == 0 ? 0 : x - 1;
      const int x_right = x + 1 >= w ? w - 1 : x + 1;
      const std::int32_t x_current_prev = x_previous_index_map[x];
      const float *nw = neighbor_weights + idx * kNeighborCount;
      const float *image_px = image + rgb_pixel_base(idx);
      float foreground_weighted_sum[kChannels] {};
      float background_weighted_sum[kChannels] {};

      auto accumulate_neighbor = [&](int direction, bool use_previous, int current_y, int current_x) {
        const float *foreground_px;
        const float *background_px;
        if (use_previous) {
          const std::size_t previous_idx =
              scalar_index(static_cast<std::size_t>(y_current_prev), static_cast<std::size_t>(x_current_prev), static_cast<std::size_t>(previous_width));
          foreground_px = previous_foreground + rgb_pixel_base(previous_idx);
          background_px = previous_background + rgb_pixel_base(previous_idx);
        } else {
          const std::size_t current_idx =
              scalar_index(static_cast<std::size_t>(current_y), static_cast<std::size_t>(current_x), static_cast<std::size_t>(w));
          foreground_px = foreground + rgb_pixel_base(current_idx);
          background_px = background + rgb_pixel_base(current_idx);
        }

        apply_rgb([&]<std::size_t C>(std::integral_constant<std::size_t, C>) {
          foreground_weighted_sum[C] += nw[direction] * foreground_px[C];
          background_weighted_sum[C] += nw[direction] * background_px[C];
        });
      };

      accumulate_neighbor(0, x_left == x, y, x_left);
      accumulate_neighbor(1, x_right == x, y, x_right);
      accumulate_neighbor(2, y_up == y, y_up, x);
      accumulate_neighbor(3, y_down == y, y_down, x);

      const PixelSolutionInputs inputs = make_pixel_solution_inputs(
          alpha[idx],
          image_px,
          foreground_weighted_sum,
          background_weighted_sum,
          inverse_weight_sum[idx],
          inverse_weight_sum_plus_one[idx],
          foreground_gain[idx],
          background_gain[idx]);
      write_solution_buffer(foreground, background, idx, inputs);
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
  update_red_black_half_step_from_previous_level_buffer<false>(
      foreground.data(),
      background.data(),
      image.data(),
      alpha.data(),
      neighbor_weights.data(),
      inverse_weight_sum.data(),
      inverse_weight_sum_plus_one.data(),
      foreground_gain.data(),
      background_gain.data(),
      previous_foreground.data(),
      previous_background.data(),
      x_previous_index_map.data(),
      y_previous_index_map.data(),
      h,
      w,
      static_cast<int>(previous_foreground.shape(1)));
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
  update_red_black_half_step_from_previous_level_buffer<true>(
      foreground.data(),
      background.data(),
      image.data(),
      alpha.data(),
      neighbor_weights.data(),
      inverse_weight_sum.data(),
      inverse_weight_sum_plus_one.data(),
      foreground_gain.data(),
      background_gain.data(),
      previous_foreground.data(),
      previous_background.data(),
      x_previous_index_map.data(),
      y_previous_index_map.data(),
      h,
      w,
      static_cast<int>(previous_foreground.shape(1)));
}

}  // namespace
