#include "fastmlfe2_ffi.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <vector>

#include <opencv2/core/mat.hpp>
#include <opencv2/imgproc.hpp>

namespace {

constexpr std::array<std::pair<int, int>, 4> kFourOffsets{{
    {0, -1}, {0, 1}, {-1, 0}, {1, 0},
}};
constexpr float kPseudoInverseEps = 1.0e-8f;

struct PixelLevelOperator {
  std::size_t state_index{};
  std::array<std::size_t, 4> neighbor_indices{};
  // Lean's weightedMeans is Σ w_ij * value_j / s_i. We pre-normalize to
  // λ_ij = w_ij / s_i at build time so the runtime kernel can apply the
  // same operator without carrying total_weight through each iteration.
  std::array<float, 4> normalized_weights{};
  float total_weight = 0.0f;
  float self_weight = 0.0f;
  float alpha = 0.0f;
  float beta = 0.0f;
  float inv_level_denom = 0.0f;
};

struct BuiltLevelOperator {
  std::vector<PixelLevelOperator> pixels{};
  std::vector<std::size_t> red_pixel_indices{};
  std::vector<std::size_t> black_pixel_indices{};
};

struct RefinePair {
  float fg = 0.0f;
  float bg = 0.0f;
};

struct RgbLinearSystemBuffers {
  int width = 0;
  int height = 0;
  int stride = 0;
  std::vector<float> fg_red{};
  std::vector<float> fg_green{};
  std::vector<float> fg_blue{};
  std::vector<float> bg_red{};
  std::vector<float> bg_green{};
  std::vector<float> bg_blue{};
};

struct VCycleLevelData {
  int width = 0;
  int height = 0;
  int stride = 0;
  std::vector<float> alpha{};
  BuiltLevelOperator level_operator{};
};

bool valid_dims(int width, int height) {
  return width > 0 && height > 0;
}

bool valid_stride(int stride, int width) {
  return stride >= width;
}

bool overlaps(const float *a, const float *b, std::size_t count) {
  auto *a_begin = reinterpret_cast<const unsigned char *>(a);
  auto *a_end = a_begin + count * sizeof(float);
  auto *b_begin = reinterpret_cast<const unsigned char *>(b);
  auto *b_end = b_begin + count * sizeof(float);
  return a_begin < b_end && b_begin < a_end;
}

template <std::size_t InputCount, std::size_t OutputCount>
bool has_output_alias(
    const std::array<const float *, InputCount> &inputs,
    const std::array<float *, OutputCount> &outputs,
    std::size_t count) {
  for (float *output : outputs) {
    for (const float *input : inputs) {
      if (overlaps(input, output, count)) {
        return true;
      }
    }
  }
  for (std::size_t i = 0; i < outputs.size(); ++i) {
    for (std::size_t j = i + 1; j < outputs.size(); ++j) {
      if (overlaps(outputs[i], outputs[j], count)) {
        return true;
      }
    }
  }
  return false;
}

int validate_gray_buffer(const float *buf, int width, int height, int stride) {
  if (buf == nullptr) {
    return FASTMLFE2_STATUS_NULL_POINTER;
  }
  if (!valid_dims(width, height)) {
    return FASTMLFE2_STATUS_INVALID_DIMENSIONS;
  }
  if (!valid_stride(stride, width)) {
    return FASTMLFE2_STATUS_INVALID_STRIDE;
  }
  return FASTMLFE2_STATUS_OK;
}

int validate_mut_gray_buffer(float *buf, int width, int height, int stride) {
  return validate_gray_buffer(buf, width, height, stride);
}

int clamp_index(int value, int upper) {
  return std::clamp(value, 0, upper - 1);
}

float load_at(const float *buf, int stride, int x, int y) {
  return buf[static_cast<std::size_t>(y) * static_cast<std::size_t>(stride) +
             static_cast<std::size_t>(x)];
}

void store_at(float *buf, int stride, int x, int y, float value) {
  buf[static_cast<std::size_t>(y) * static_cast<std::size_t>(stride) +
      static_cast<std::size_t>(x)] = value;
}

std::size_t flat_index(int stride, int x, int y) {
  return static_cast<std::size_t>(y) * static_cast<std::size_t>(stride) +
         static_cast<std::size_t>(x);
}

RefinePair compute_weighted_means(
    const PixelLevelOperator &pixel,
    const float *fg,
    const float *bg) {
  RefinePair means;
  for (std::size_t i = 0; i < pixel.neighbor_indices.size(); ++i) {
    const std::size_t idx = pixel.neighbor_indices[i];
    const float lambda = pixel.normalized_weights[i];
    means.fg += lambda * fg[idx];
    means.bg += lambda * bg[idx];
  }
  return means;
}

RefinePair apply_mean_residual_correction(
    const PixelLevelOperator &pixel,
    float image,
    const float *fg,
    const float *bg) {
  const RefinePair means = compute_weighted_means(pixel, fg, bg);
  const float residual = image - pixel.alpha * means.fg - pixel.beta * means.bg;
  return {
      .fg = means.fg + pixel.alpha * pixel.inv_level_denom * residual,
      .bg = means.bg + pixel.beta * pixel.inv_level_denom * residual,
  };
}

RefinePair apply_global_system(
    const PixelLevelOperator &pixel,
    const float *fg,
    const float *bg) {
  const RefinePair means = compute_weighted_means(pixel, fg, bg);
  const float fg_center = fg[pixel.state_index];
  const float bg_center = bg[pixel.state_index];
  const float compositing_value =
      pixel.alpha * fg_center + pixel.beta * bg_center;
  return {
      .fg =
          pixel.total_weight * (fg_center - means.fg) +
          pixel.alpha * compositing_value,
      .bg =
          pixel.total_weight * (bg_center - means.bg) +
          pixel.beta * compositing_value,
  };
}

RefinePair compute_local_linear_residual(
    const PixelLevelOperator &pixel,
    float image,
    const float *fg,
    const float *bg) {
  const RefinePair system_apply = apply_global_system(pixel, fg, bg);
  return {
      .fg = system_apply.fg - pixel.alpha * image,
      .bg = system_apply.bg - pixel.beta * image,
  };
}

float compute_local_residual_inf_norm(
    const PixelLevelOperator &pixel,
    float image,
    const float *fg,
    const float *bg) {
  const RefinePair residual = compute_local_linear_residual(pixel, image, fg, bg);
  return std::max(std::fabs(residual.fg), std::fabs(residual.bg));
}

RefinePair solve_global_linear_block(
    const PixelLevelOperator &pixel,
    float rhs_fg,
    float rhs_bg,
    const float *fg,
    const float *bg) {
  float offdiag_fg = 0.0f;
  float offdiag_bg = 0.0f;
  for (std::size_t i = 0; i < pixel.neighbor_indices.size(); ++i) {
    const std::size_t neighbor_index = pixel.neighbor_indices[i];
    if (neighbor_index == pixel.state_index) {
      continue;
    }
    const float weight = pixel.normalized_weights[i] * pixel.total_weight;
    offdiag_fg += weight * fg[neighbor_index];
    offdiag_bg += weight * bg[neighbor_index];
  }

  const float laplacian_diag = pixel.total_weight - pixel.self_weight;
  const float rhs0 = rhs_fg + offdiag_fg;
  const float rhs1 = rhs_bg + offdiag_bg;
  if (laplacian_diag <= kPseudoInverseEps) {
    const float norm_sq = pixel.alpha * pixel.alpha + pixel.beta * pixel.beta;
    const float scale =
        (pixel.alpha * rhs0 + pixel.beta * rhs1) / (norm_sq * norm_sq);
    return {
        .fg = pixel.alpha * scale,
        .bg = pixel.beta * scale,
    };
  }

  const float a00 = laplacian_diag + pixel.alpha * pixel.alpha;
  const float a01 = pixel.alpha * pixel.beta;
  const float a11 = laplacian_diag + pixel.beta * pixel.beta;
  const float det = a00 * a11 - a01 * a01;
  return {
      .fg = (a11 * rhs0 - a01 * rhs1) / det,
      .bg = (a00 * rhs1 - a01 * rhs0) / det,
  };
}

RefinePair compute_local_residual_from_rhs(
    const PixelLevelOperator &pixel,
    float rhs_fg,
    float rhs_bg,
    const float *fg,
    const float *bg) {
  const RefinePair system_apply = apply_global_system(pixel, fg, bg);
  return {
      .fg = system_apply.fg - rhs_fg,
      .bg = system_apply.bg - rhs_bg,
  };
}

[[maybe_unused]] void apply_level_operator_rgb_global_system(
    const BuiltLevelOperator &level_operator,
    const float *fg_red,
    const float *fg_green,
    const float *fg_blue,
    const float *bg_red,
    const float *bg_green,
    const float *bg_blue,
    float *fg_red_out,
    float *fg_green_out,
    float *fg_blue_out,
    float *bg_red_out,
    float *bg_green_out,
    float *bg_blue_out) {
  for (const PixelLevelOperator &pixel : level_operator.pixels) {
    const auto apply_channel =
        [&](const float *fg_channel,
            const float *bg_channel,
            float *fg_out,
            float *bg_out) {
          const RefinePair applied = apply_global_system(pixel, fg_channel, bg_channel);
          fg_out[pixel.state_index] = applied.fg;
          bg_out[pixel.state_index] = applied.bg;
        };
    apply_channel(fg_red, bg_red, fg_red_out, bg_red_out);
    apply_channel(fg_green, bg_green, fg_green_out, bg_green_out);
    apply_channel(fg_blue, bg_blue, fg_blue_out, bg_blue_out);
  }
}

[[maybe_unused]] void compute_level_operator_rgb_linear_residual(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    const BuiltLevelOperator &level_operator,
    const float *fg_red,
    const float *fg_green,
    const float *fg_blue,
    const float *bg_red,
    const float *bg_green,
    const float *bg_blue,
    float *fg_red_out,
    float *fg_green_out,
    float *fg_blue_out,
    float *bg_red_out,
    float *bg_green_out,
    float *bg_blue_out) {
  for (const PixelLevelOperator &pixel : level_operator.pixels) {
    const auto apply_channel =
        [&](float image,
            const float *fg_channel,
            const float *bg_channel,
            float *fg_out,
            float *bg_out) {
          const RefinePair residual =
              compute_local_linear_residual(pixel, image, fg_channel, bg_channel);
          fg_out[pixel.state_index] = residual.fg;
          bg_out[pixel.state_index] = residual.bg;
        };
    apply_channel(
        image_red[pixel.state_index], fg_red, bg_red, fg_red_out, bg_red_out);
    apply_channel(
        image_green[pixel.state_index], fg_green, bg_green, fg_green_out, bg_green_out);
    apply_channel(
        image_blue[pixel.state_index], fg_blue, bg_blue, fg_blue_out, bg_blue_out);
  }
}

PixelLevelOperator build_pixel_level_operator(
    const float *alpha,
    int width,
    int height,
    int stride,
    int x,
    int y,
    float eps_r,
    float omega) {
  PixelLevelOperator pixel;
  pixel.state_index = flat_index(stride, x, y);
  const float alpha_center = load_at(alpha, stride, x, y);
  pixel.alpha = alpha_center;
  pixel.beta = 1.0f - alpha_center;
  float total_weight = 0.0f;

  for (std::size_t i = 0; i < kFourOffsets.size(); ++i) {
    const auto &[dy, dx] = kFourOffsets[i];
    const int nx = clamp_index(x + dx, width);
    const int ny = clamp_index(y + dy, height);
    const float alpha_neighbor = load_at(alpha, stride, nx, ny);
    const float weight =
        eps_r + omega * std::fabs(alpha_center - alpha_neighbor);
    const std::size_t neighbor_index = flat_index(stride, nx, ny);
    pixel.neighbor_indices[i] = neighbor_index;
    pixel.normalized_weights[i] = weight;
    total_weight += weight;
    if (neighbor_index == pixel.state_index) {
      pixel.self_weight += weight;
    }
  }

  for (float &weight : pixel.normalized_weights) {
    weight /= total_weight;
  }
  pixel.total_weight = total_weight;
  const float level_denom =
      total_weight + pixel.alpha * pixel.alpha + pixel.beta * pixel.beta;
  pixel.inv_level_denom = 1.0f / level_denom;
  return pixel;
}

BuiltLevelOperator build_level_operator(
    const float *alpha,
    int width,
    int height,
    int stride,
    float eps_r,
    float omega) {
  const std::size_t pixel_count =
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  BuiltLevelOperator level_operator;
  level_operator.pixels.resize(pixel_count);
  level_operator.red_pixel_indices.reserve((pixel_count + 1) / 2);
  level_operator.black_pixel_indices.reserve(pixel_count / 2);
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const std::size_t pixel_index =
          static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
          static_cast<std::size_t>(x);
      level_operator.pixels[pixel_index] =
          build_pixel_level_operator(alpha, width, height, stride, x, y, eps_r, omega);
      if ((x + y) % 2 == 0) {
        level_operator.red_pixel_indices.push_back(pixel_index);
      } else {
        level_operator.black_pixel_indices.push_back(pixel_index);
      }
    }
  }
  return level_operator;
}

void apply_level_operator_gray_pass(
    const float *image,
    const BuiltLevelOperator &level_operator,
    float *fg_state,
    float *bg_state) {
  for (const PixelLevelOperator &pixel : level_operator.pixels) {
    const RefinePair result =
        apply_mean_residual_correction(pixel, image[pixel.state_index], fg_state, bg_state);
    fg_state[pixel.state_index] = std::clamp(result.fg, 0.0f, 1.0f);
    bg_state[pixel.state_index] = std::clamp(result.bg, 0.0f, 1.0f);
  }
}

float apply_level_operator_rgb_half_pass(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    const BuiltLevelOperator &level_operator,
    const std::vector<std::size_t> &active_pixels,
    float *fg_red,
    float *fg_green,
    float *fg_blue,
    float *bg_red,
    float *bg_green,
    float *bg_blue,
    bool track_update) {
  float max_update = 0.0f;
  for (std::size_t pixel_index : active_pixels) {
    const PixelLevelOperator &pixel = level_operator.pixels[pixel_index];
    const auto apply_channel =
        [&](const float *image_channel, float *fg_channel, float *bg_channel) {
          const RefinePair result =
              apply_mean_residual_correction(
                  pixel,
                  image_channel[pixel.state_index],
                  fg_channel,
                  bg_channel);
          const float new_fg = std::clamp(result.fg, 0.0f, 1.0f);
          const float new_bg = std::clamp(result.bg, 0.0f, 1.0f);
          if (track_update) {
            max_update = std::max(max_update, std::fabs(new_fg - fg_channel[pixel.state_index]));
            max_update = std::max(max_update, std::fabs(new_bg - bg_channel[pixel.state_index]));
          }
          fg_channel[pixel.state_index] = new_fg;
          bg_channel[pixel.state_index] = new_bg;
        };
    apply_channel(image_red, fg_red, bg_red);
    apply_channel(image_green, fg_green, bg_green);
    apply_channel(image_blue, fg_blue, bg_blue);
  }
  return max_update;
}

float compute_level_operator_rgb_residual_inf_norm(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    const BuiltLevelOperator &level_operator,
    const float *fg_red,
    const float *fg_green,
    const float *fg_blue,
    const float *bg_red,
    const float *bg_green,
    const float *bg_blue) {
  float max_residual = 0.0f;
  for (const PixelLevelOperator &pixel : level_operator.pixels) {
    max_residual = std::max(
        max_residual,
        compute_local_residual_inf_norm(pixel, image_red[pixel.state_index], fg_red, bg_red));
    max_residual = std::max(
        max_residual,
        compute_local_residual_inf_norm(pixel, image_green[pixel.state_index], fg_green, bg_green));
    max_residual = std::max(
        max_residual,
        compute_local_residual_inf_norm(pixel, image_blue[pixel.state_index], fg_blue, bg_blue));
  }
  return max_residual;
}

int choose_interpolation(int src_w, int src_h, int dst_w, int dst_h) {
  if (dst_w < src_w || dst_h < src_h) {
    return cv::INTER_AREA;
  }
  return cv::INTER_LINEAR;
}

int resize_gray(
    const float *src,
    int src_w,
    int src_h,
    int src_stride,
    float *dst,
    int dst_w,
    int dst_h,
    int dst_stride,
    int interpolation) {
  int rc = validate_gray_buffer(src, src_w, src_h, src_stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(dst, dst_w, dst_h, dst_stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }

  cv::Mat src_mat(src_h, src_w, CV_32FC1,
                  const_cast<float *>(src),
                  static_cast<std::size_t>(src_stride) * sizeof(float));
  cv::Mat dst_mat(dst_h, dst_w, CV_32FC1,
                  dst,
                  static_cast<std::size_t>(dst_stride) * sizeof(float));
  cv::resize(src_mat, dst_mat, cv::Size(dst_w, dst_h), 0.0, 0.0, interpolation);
  return FASTMLFE2_STATUS_OK;
}

RgbLinearSystemBuffers alloc_rgb_buffers(int width, int height) {
  const std::size_t count =
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  return {
      .width = width,
      .height = height,
      .stride = width,
      .fg_red = std::vector<float>(count),
      .fg_green = std::vector<float>(count),
      .fg_blue = std::vector<float>(count),
      .bg_red = std::vector<float>(count),
      .bg_green = std::vector<float>(count),
      .bg_blue = std::vector<float>(count),
  };
}

void copy_strided_to_contiguous(
    const float *src,
    int width,
    int height,
    int src_stride,
    std::vector<float> *dst) {
  dst->resize(static_cast<std::size_t>(width) * static_cast<std::size_t>(height));
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      (*dst)[flat_index(width, x, y)] = src[flat_index(src_stride, x, y)];
    }
  }
}

void copy_contiguous_to_strided(
    const std::vector<float> &src,
    int width,
    int height,
    float *dst,
    int dst_stride) {
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      dst[flat_index(dst_stride, x, y)] = src[flat_index(width, x, y)];
    }
  }
}

int resize_rgb_buffers(
    const RgbLinearSystemBuffers &src,
    RgbLinearSystemBuffers *dst) {
  const int interpolation =
      choose_interpolation(src.width, src.height, dst->width, dst->height);
  int rc = resize_gray(
      src.fg_red.data(), src.width, src.height, src.stride,
      dst->fg_red.data(), dst->width, dst->height, dst->stride,
      interpolation);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = resize_gray(
      src.fg_green.data(), src.width, src.height, src.stride,
      dst->fg_green.data(), dst->width, dst->height, dst->stride,
      interpolation);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = resize_gray(
      src.fg_blue.data(), src.width, src.height, src.stride,
      dst->fg_blue.data(), dst->width, dst->height, dst->stride,
      interpolation);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = resize_gray(
      src.bg_red.data(), src.width, src.height, src.stride,
      dst->bg_red.data(), dst->width, dst->height, dst->stride,
      interpolation);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = resize_gray(
      src.bg_green.data(), src.width, src.height, src.stride,
      dst->bg_green.data(), dst->width, dst->height, dst->stride,
      interpolation);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  return resize_gray(
      src.bg_blue.data(), src.width, src.height, src.stride,
      dst->bg_blue.data(), dst->width, dst->height, dst->stride,
      interpolation);
}

RgbLinearSystemBuffers build_image_rhs(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    const float *alpha,
    int width,
    int height,
    int stride) {
  RgbLinearSystemBuffers rhs = alloc_rgb_buffers(width, height);
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const std::size_t src_index = flat_index(stride, x, y);
      const std::size_t dst_index = flat_index(width, x, y);
      const float alpha_value = alpha[src_index];
      const float beta_value = 1.0f - alpha_value;
      rhs.fg_red[dst_index] = alpha_value * image_red[src_index];
      rhs.fg_green[dst_index] = alpha_value * image_green[src_index];
      rhs.fg_blue[dst_index] = alpha_value * image_blue[src_index];
      rhs.bg_red[dst_index] = beta_value * image_red[src_index];
      rhs.bg_green[dst_index] = beta_value * image_green[src_index];
      rhs.bg_blue[dst_index] = beta_value * image_blue[src_index];
    }
  }
  return rhs;
}

float residual_inf_norm(const RgbLinearSystemBuffers &residual) {
  float max_residual = 0.0f;
  const auto update_max = [&](const std::vector<float> &channel) {
    for (float value : channel) {
      max_residual = std::max(max_residual, std::fabs(value));
    }
  };
  update_max(residual.fg_red);
  update_max(residual.fg_green);
  update_max(residual.fg_blue);
  update_max(residual.bg_red);
  update_max(residual.bg_green);
  update_max(residual.bg_blue);
  return max_residual;
}

void subtract_rgb_buffers(
    RgbLinearSystemBuffers *state,
    const RgbLinearSystemBuffers &correction) {
  const auto subtract_channel =
      [](std::vector<float> *dst, const std::vector<float> &src) {
        for (std::size_t i = 0; i < dst->size(); ++i) {
          (*dst)[i] -= src[i];
        }
      };
  subtract_channel(&state->fg_red, correction.fg_red);
  subtract_channel(&state->fg_green, correction.fg_green);
  subtract_channel(&state->fg_blue, correction.fg_blue);
  subtract_channel(&state->bg_red, correction.bg_red);
  subtract_channel(&state->bg_green, correction.bg_green);
  subtract_channel(&state->bg_blue, correction.bg_blue);
}

float smooth_level_operator_rgb_half_pass_from_rhs(
    const BuiltLevelOperator &level_operator,
    const std::vector<std::size_t> &active_pixels,
    const float *rhs_fg_red,
    const float *rhs_fg_green,
    const float *rhs_fg_blue,
    const float *rhs_bg_red,
    const float *rhs_bg_green,
    const float *rhs_bg_blue,
    float *fg_red,
    float *fg_green,
    float *fg_blue,
    float *bg_red,
    float *bg_green,
    float *bg_blue,
    bool track_update) {
  float max_update = 0.0f;
  for (std::size_t pixel_index : active_pixels) {
    const PixelLevelOperator &pixel = level_operator.pixels[pixel_index];
    const auto apply_channel =
        [&](float rhs_fg,
            float rhs_bg,
            float *fg_channel,
            float *bg_channel) {
          const RefinePair solved =
              solve_global_linear_block(pixel, rhs_fg, rhs_bg, fg_channel, bg_channel);
          if (track_update) {
            max_update =
                std::max(max_update, std::fabs(solved.fg - fg_channel[pixel.state_index]));
            max_update =
                std::max(max_update, std::fabs(solved.bg - bg_channel[pixel.state_index]));
          }
          fg_channel[pixel.state_index] = solved.fg;
          bg_channel[pixel.state_index] = solved.bg;
        };
    apply_channel(
        rhs_fg_red[pixel.state_index], rhs_bg_red[pixel.state_index], fg_red, bg_red);
    apply_channel(
        rhs_fg_green[pixel.state_index], rhs_bg_green[pixel.state_index], fg_green, bg_green);
    apply_channel(
        rhs_fg_blue[pixel.state_index], rhs_bg_blue[pixel.state_index], fg_blue, bg_blue);
  }
  return max_update;
}

void rbgs_smooth_level_rgb_from_rhs(
    const BuiltLevelOperator &level_operator,
    const RgbLinearSystemBuffers &rhs,
    RgbLinearSystemBuffers *state,
    int iterations) {
  for (int iteration = 0; iteration < iterations; ++iteration) {
    smooth_level_operator_rgb_half_pass_from_rhs(
        level_operator, level_operator.red_pixel_indices,
        rhs.fg_red.data(), rhs.fg_green.data(), rhs.fg_blue.data(),
        rhs.bg_red.data(), rhs.bg_green.data(), rhs.bg_blue.data(),
        state->fg_red.data(), state->fg_green.data(), state->fg_blue.data(),
        state->bg_red.data(), state->bg_green.data(), state->bg_blue.data(),
        false);
    smooth_level_operator_rgb_half_pass_from_rhs(
        level_operator, level_operator.black_pixel_indices,
        rhs.fg_red.data(), rhs.fg_green.data(), rhs.fg_blue.data(),
        rhs.bg_red.data(), rhs.bg_green.data(), rhs.bg_blue.data(),
        state->fg_red.data(), state->fg_green.data(), state->fg_blue.data(),
        state->bg_red.data(), state->bg_green.data(), state->bg_blue.data(),
        false);
  }
}

void compute_level_operator_rgb_residual_from_rhs(
    const BuiltLevelOperator &level_operator,
    const RgbLinearSystemBuffers &rhs,
    const RgbLinearSystemBuffers &state,
    RgbLinearSystemBuffers *residual) {
  for (const PixelLevelOperator &pixel : level_operator.pixels) {
    const auto apply_channel =
        [&](float rhs_fg,
            float rhs_bg,
            const float *fg_channel,
            const float *bg_channel,
            float *fg_out,
            float *bg_out) {
          const RefinePair residual_pair = compute_local_residual_from_rhs(
              pixel, rhs_fg, rhs_bg, fg_channel, bg_channel);
          fg_out[pixel.state_index] = residual_pair.fg;
          bg_out[pixel.state_index] = residual_pair.bg;
        };
    apply_channel(
        rhs.fg_red[pixel.state_index], rhs.bg_red[pixel.state_index],
        state.fg_red.data(), state.bg_red.data(),
        residual->fg_red.data(), residual->bg_red.data());
    apply_channel(
        rhs.fg_green[pixel.state_index], rhs.bg_green[pixel.state_index],
        state.fg_green.data(), state.bg_green.data(),
        residual->fg_green.data(), residual->bg_green.data());
    apply_channel(
        rhs.fg_blue[pixel.state_index], rhs.bg_blue[pixel.state_index],
        state.fg_blue.data(), state.bg_blue.data(),
        residual->fg_blue.data(), residual->bg_blue.data());
  }
}

int round_float_to_int_at_least_one(double value) {
  return std::max(1, static_cast<int>(std::llround(value)));
}

int level_size_at(int size, int level, int level_count) {
  if (level_count <= 0) {
    return size;
  }
  return round_float_to_int_at_least_one(
      std::pow(static_cast<double>(size),
               static_cast<double>(level) / static_cast<double>(level_count)));
}

std::vector<std::pair<int, int>> build_vcycle_level_sizes(
    int width,
    int height,
    int level_count) {
  if (level_count <= 1) {
    return {{width, height}};
  }
  std::vector<std::pair<int, int>> sizes;
  sizes.reserve(static_cast<std::size_t>(level_count));
  const int denom = level_count - 1;
  for (int level = 0; level < level_count; ++level) {
    const std::pair<int, int> size{
        level_size_at(width, level, denom),
        level_size_at(height, level, denom),
    };
    if (sizes.empty() || sizes.back() != size) {
      sizes.push_back(size);
    }
  }
  if (sizes.empty() || sizes.back() != std::pair<int, int>{width, height}) {
    sizes.push_back({width, height});
  }
  return sizes;
}

int build_vcycle_levels(
    const float *alpha,
    int width,
    int height,
    int stride,
    int level_count,
    float eps_r,
    float omega,
    std::vector<VCycleLevelData> *levels) {
  levels->clear();
  const auto sizes = build_vcycle_level_sizes(width, height, level_count);
  levels->reserve(sizes.size());
  for (const auto &[level_width, level_height] : sizes) {
    VCycleLevelData level;
    level.width = level_width;
    level.height = level_height;
    level.stride = level_width;
    level.alpha.resize(
        static_cast<std::size_t>(level_width) * static_cast<std::size_t>(level_height));
    int rc = resize_gray(
        alpha, width, height, stride,
        level.alpha.data(), level_width, level_height, level.stride,
        cv::INTER_NEAREST);
    if (rc != FASTMLFE2_STATUS_OK) {
      return rc;
    }
    level.level_operator =
        build_level_operator(level.alpha.data(), level_width, level_height, level.stride,
                             eps_r, omega);
    levels->push_back(std::move(level));
  }
  return FASTMLFE2_STATUS_OK;
}

int run_vcycle_recursive(
    const std::vector<VCycleLevelData> &levels,
    int level_index,
    const RgbLinearSystemBuffers &rhs,
    RgbLinearSystemBuffers *state,
    int pre_smoothing,
    int post_smoothing,
    int coarse_iterations) {
  const VCycleLevelData &level = levels[static_cast<std::size_t>(level_index)];
  if (level_index == 0) {
    rbgs_smooth_level_rgb_from_rhs(
        level.level_operator, rhs, state, coarse_iterations);
    return FASTMLFE2_STATUS_OK;
  }

  rbgs_smooth_level_rgb_from_rhs(
      level.level_operator, rhs, state, pre_smoothing);
  RgbLinearSystemBuffers residual = alloc_rgb_buffers(level.width, level.height);
  compute_level_operator_rgb_residual_from_rhs(
      level.level_operator, rhs, *state, &residual);

  const VCycleLevelData &coarse = levels[static_cast<std::size_t>(level_index - 1)];
  RgbLinearSystemBuffers coarse_rhs = alloc_rgb_buffers(coarse.width, coarse.height);
  int rc = resize_rgb_buffers(residual, &coarse_rhs);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  RgbLinearSystemBuffers coarse_correction =
      alloc_rgb_buffers(coarse.width, coarse.height);
  rc = run_vcycle_recursive(
      levels, level_index - 1, coarse_rhs, &coarse_correction,
      pre_smoothing, post_smoothing, coarse_iterations);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }

  RgbLinearSystemBuffers fine_correction = alloc_rgb_buffers(level.width, level.height);
  rc = resize_rgb_buffers(coarse_correction, &fine_correction);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  subtract_rgb_buffers(state, fine_correction);
  rbgs_smooth_level_rgb_from_rhs(
      level.level_operator, rhs, state, post_smoothing);
  return FASTMLFE2_STATUS_OK;
}

}  // namespace

extern "C" int fastmlfe2_resize_float_gray(
    const float *src,
    int src_w,
    int src_h,
    int src_stride,
    float *dst,
    int dst_w,
    int dst_h,
    int dst_stride) {
  return resize_gray(
      src, src_w, src_h, src_stride,
      dst, dst_w, dst_h, dst_stride,
      choose_interpolation(src_w, src_h, dst_w, dst_h));
}

extern "C" int fastmlfe2_resize_float_gray_nearest(
    const float *src,
    int src_w,
    int src_h,
    int src_stride,
    float *dst,
    int dst_w,
    int dst_h,
    int dst_stride) {
  return resize_gray(
      src, src_w, src_h, src_stride,
      dst, dst_w, dst_h, dst_stride,
      cv::INTER_NEAREST);
}

extern "C" int fastmlfe2_reference_refine_gray_single_pass(
    const float *image,
    const float *alpha,
    const float *fg,
    const float *bg,
    float *fg_out,
    float *bg_out,
    int width,
    int height,
    int stride,
    float eps_r,
    float omega) {
  int rc = validate_gray_buffer(image, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(alpha, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  if (eps_r <= 0.0f || omega < 0.0f) {
    return FASTMLFE2_STATUS_INVALID_PARAMS;
  }

  const std::size_t count =
      static_cast<std::size_t>(height) * static_cast<std::size_t>(stride);
  if (has_output_alias(
          std::array<const float *, 4>{image, alpha, fg, bg},
          std::array<float *, 2>{fg_out, bg_out},
          count)) {
    return FASTMLFE2_STATUS_ALIASING;
  }

  std::copy(fg, fg + count, fg_out);
  std::copy(bg, bg + count, bg_out);
  const BuiltLevelOperator level_operator =
      build_level_operator(alpha, width, height, stride, eps_r, omega);
  apply_level_operator_gray_pass(image, level_operator, fg_out, bg_out);
  return FASTMLFE2_STATUS_OK;
}

extern "C" int fastmlfe2_reference_refine_rgb(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    const float *alpha,
    const float *fg_red,
    const float *fg_green,
    const float *fg_blue,
    const float *bg_red,
    const float *bg_green,
    const float *bg_blue,
    float *fg_red_out,
    float *fg_green_out,
    float *fg_blue_out,
    float *bg_red_out,
    float *bg_green_out,
    float *bg_blue_out,
    int width,
    int height,
    int stride,
    int iterations,
    float eps_r,
    float omega,
    float residual_tol,
    float update_tol) {
  int rc = validate_gray_buffer(image_red, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(image_green, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(image_blue, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(alpha, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg_red, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg_green, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg_blue, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg_red, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg_green, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg_blue, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_red_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_green_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_blue_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_red_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_green_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_blue_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  if (iterations < 0 || eps_r <= 0.0f || omega < 0.0f ||
      residual_tol < 0.0f || update_tol < 0.0f) {
    return FASTMLFE2_STATUS_INVALID_PARAMS;
  }

  const std::size_t count =
      static_cast<std::size_t>(height) * static_cast<std::size_t>(stride);
  if (has_output_alias(
          std::array<const float *, 10>{
              image_red, image_green, image_blue, alpha,
              fg_red, fg_green, fg_blue, bg_red, bg_green, bg_blue},
          std::array<float *, 6>{
              fg_red_out, fg_green_out, fg_blue_out,
              bg_red_out, bg_green_out, bg_blue_out},
          count)) {
    return FASTMLFE2_STATUS_ALIASING;
  }

  std::copy(fg_red, fg_red + count, fg_red_out);
  std::copy(fg_green, fg_green + count, fg_green_out);
  std::copy(fg_blue, fg_blue + count, fg_blue_out);
  std::copy(bg_red, bg_red + count, bg_red_out);
  std::copy(bg_green, bg_green + count, bg_green_out);
  std::copy(bg_blue, bg_blue + count, bg_blue_out);

  const BuiltLevelOperator level_operator =
      build_level_operator(alpha, width, height, stride, eps_r, omega);
  for (int iteration = 0; iteration < iterations; ++iteration) {
    float max_update = 0.0f;
    max_update = std::max(
        max_update,
        apply_level_operator_rgb_half_pass(
            image_red, image_green, image_blue,
            level_operator, level_operator.red_pixel_indices,
            fg_red_out, fg_green_out, fg_blue_out,
            bg_red_out, bg_green_out, bg_blue_out,
            update_tol > 0.0f));
    max_update = std::max(
        max_update,
        apply_level_operator_rgb_half_pass(
            image_red, image_green, image_blue,
            level_operator, level_operator.black_pixel_indices,
            fg_red_out, fg_green_out, fg_blue_out,
            bg_red_out, bg_green_out, bg_blue_out,
            update_tol > 0.0f));
    float max_residual = 0.0f;
    if (residual_tol > 0.0f) {
      max_residual = compute_level_operator_rgb_residual_inf_norm(
          image_red, image_green, image_blue,
          level_operator,
          fg_red_out, fg_green_out, fg_blue_out,
          bg_red_out, bg_green_out, bg_blue_out);
    }
    bool has_active_stop = false;
    bool converged = true;
    if (residual_tol > 0.0f) {
      has_active_stop = true;
      converged = converged && max_residual <= residual_tol;
    }
    if (update_tol > 0.0f) {
      has_active_stop = true;
      converged = converged && max_update <= update_tol;
    }
    if (has_active_stop && converged) {
      break;
    }
  }
  return FASTMLFE2_STATUS_OK;
}

extern "C" int fastmlfe2_global_spd_vcycle_rgb(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    const float *alpha,
    const float *fg_red,
    const float *fg_green,
    const float *fg_blue,
    const float *bg_red,
    const float *bg_green,
    const float *bg_blue,
    float *fg_red_out,
    float *fg_green_out,
    float *fg_blue_out,
    float *bg_red_out,
    float *bg_green_out,
    float *bg_blue_out,
    int width,
    int height,
    int stride,
    int level_count,
    int max_cycles,
    int pre_smoothing,
    int post_smoothing,
    int coarse_iterations,
    float eps_r,
    float omega,
    float residual_tol) {
  int rc = validate_gray_buffer(image_red, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(image_green, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(image_blue, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(alpha, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg_red, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg_green, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(fg_blue, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg_red, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg_green, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_gray_buffer(bg_blue, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_red_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_green_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(fg_blue_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_red_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_green_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  rc = validate_mut_gray_buffer(bg_blue_out, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }
  if (level_count <= 0 || max_cycles < 0 || pre_smoothing < 0 ||
      post_smoothing < 0 || coarse_iterations < 0 || eps_r <= 0.0f ||
      omega < 0.0f || residual_tol < 0.0f) {
    return FASTMLFE2_STATUS_INVALID_PARAMS;
  }

  const std::size_t count =
      static_cast<std::size_t>(height) * static_cast<std::size_t>(stride);
  if (has_output_alias(
          std::array<const float *, 10>{
              image_red, image_green, image_blue, alpha,
              fg_red, fg_green, fg_blue, bg_red, bg_green, bg_blue},
          std::array<float *, 6>{
              fg_red_out, fg_green_out, fg_blue_out,
              bg_red_out, bg_green_out, bg_blue_out},
          count)) {
    return FASTMLFE2_STATUS_ALIASING;
  }

  RgbLinearSystemBuffers state = alloc_rgb_buffers(width, height);
  copy_strided_to_contiguous(fg_red, width, height, stride, &state.fg_red);
  copy_strided_to_contiguous(fg_green, width, height, stride, &state.fg_green);
  copy_strided_to_contiguous(fg_blue, width, height, stride, &state.fg_blue);
  copy_strided_to_contiguous(bg_red, width, height, stride, &state.bg_red);
  copy_strided_to_contiguous(bg_green, width, height, stride, &state.bg_green);
  copy_strided_to_contiguous(bg_blue, width, height, stride, &state.bg_blue);

  const RgbLinearSystemBuffers rhs =
      build_image_rhs(image_red, image_green, image_blue, alpha, width, height, stride);
  std::vector<VCycleLevelData> levels;
  rc = build_vcycle_levels(
      alpha, width, height, stride, level_count, eps_r, omega, &levels);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }

  for (int cycle = 0; cycle < max_cycles; ++cycle) {
    rc = run_vcycle_recursive(
        levels, static_cast<int>(levels.size()) - 1, rhs, &state,
        pre_smoothing, post_smoothing, coarse_iterations);
    if (rc != FASTMLFE2_STATUS_OK) {
      return rc;
    }
    if (residual_tol > 0.0f) {
      RgbLinearSystemBuffers residual = alloc_rgb_buffers(width, height);
      compute_level_operator_rgb_residual_from_rhs(
          levels.back().level_operator, rhs, state, &residual);
      if (residual_inf_norm(residual) <= residual_tol) {
        break;
      }
    }
  }

  copy_contiguous_to_strided(state.fg_red, width, height, fg_red_out, stride);
  copy_contiguous_to_strided(state.fg_green, width, height, fg_green_out, stride);
  copy_contiguous_to_strided(state.fg_blue, width, height, fg_blue_out, stride);
  copy_contiguous_to_strided(state.bg_red, width, height, bg_red_out, stride);
  copy_contiguous_to_strided(state.bg_green, width, height, bg_green_out, stride);
  copy_contiguous_to_strided(state.bg_blue, width, height, bg_blue_out, stride);
  return FASTMLFE2_STATUS_OK;
}

extern "C" int fastmlfe2_clamp01_gray(float *buf, int width, int height, int stride) {
  int rc = validate_mut_gray_buffer(buf, width, height, stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return rc;
  }

  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const float value = load_at(buf, stride, x, y);
      store_at(buf, stride, x, y, std::clamp(value, 0.0f, 1.0f));
    }
  }

  return FASTMLFE2_STATUS_OK;
}
