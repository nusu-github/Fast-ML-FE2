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

struct PixelLevelOperator {
  std::array<std::size_t, 4> neighbor_indices{};
  // Lean's weightedMeans is Σ w_ij * value_j / s_i. We pre-normalize to
  // λ_ij = w_ij / s_i at build time so the runtime kernel can apply the
  // same operator without carrying total_weight through each iteration.
  std::array<float, 4> normalized_weights{};
  float alpha = 0.0f;
  float beta = 0.0f;
  float inv_level_denom = 0.0f;
};

struct RefinePair {
  float fg = 0.0f;
  float bg = 0.0f;
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
    pixel.neighbor_indices[i] = flat_index(stride, nx, ny);
    pixel.normalized_weights[i] = weight;
    total_weight += weight;
  }

  for (float &weight : pixel.normalized_weights) {
    weight /= total_weight;
  }
  const float level_denom =
      total_weight + pixel.alpha * pixel.alpha + pixel.beta * pixel.beta;
  pixel.inv_level_denom = 1.0f / level_denom;
  return pixel;
}

std::vector<PixelLevelOperator> build_level_operator(
    const float *alpha,
    int width,
    int height,
    int stride,
    float eps_r,
    float omega) {
  std::vector<PixelLevelOperator> level_operator(
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height));
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      level_operator[static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
                     static_cast<std::size_t>(x)] =
          build_pixel_level_operator(alpha, width, height, stride, x, y, eps_r, omega);
    }
  }
  return level_operator;
}

void apply_level_operator_gray_pass(
    const float *image,
    int width,
    int height,
    int stride,
    const std::vector<PixelLevelOperator> &level_operator,
    float *fg_state,
    float *bg_state) {
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const PixelLevelOperator &pixel =
          level_operator[static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
                         static_cast<std::size_t>(x)];
      const float image_center = load_at(image, stride, x, y);
      const RefinePair result =
          apply_mean_residual_correction(pixel, image_center, fg_state, bg_state);
      store_at(fg_state, stride, x, y, std::clamp(result.fg, 0.0f, 1.0f));
      store_at(bg_state, stride, x, y, std::clamp(result.bg, 0.0f, 1.0f));
    }
  }
}

void apply_level_operator_rgb_pass(
    const float *image_red,
    const float *image_green,
    const float *image_blue,
    int width,
    int height,
    int stride,
    const std::vector<PixelLevelOperator> &level_operator,
    float *fg_red,
    float *fg_green,
    float *fg_blue,
    float *bg_red,
    float *bg_green,
    float *bg_blue) {
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const PixelLevelOperator &pixel =
          level_operator[static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
                         static_cast<std::size_t>(x)];
      const auto apply_channel =
          [&](const float *image_channel, float *fg_channel, float *bg_channel) {
            const RefinePair result =
                apply_mean_residual_correction(
                    pixel,
                    load_at(image_channel, stride, x, y),
                    fg_channel,
                    bg_channel);
            store_at(fg_channel, stride, x, y, std::clamp(result.fg, 0.0f, 1.0f));
            store_at(bg_channel, stride, x, y, std::clamp(result.bg, 0.0f, 1.0f));
          };
      apply_channel(image_red, fg_red, bg_red);
      apply_channel(image_green, fg_green, bg_green);
      apply_channel(image_blue, fg_blue, bg_blue);
    }
  }
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
  const std::vector<PixelLevelOperator> level_operator =
      build_level_operator(alpha, width, height, stride, eps_r, omega);
  apply_level_operator_gray_pass(
      image, width, height, stride, level_operator, fg_out, bg_out);
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
    float omega) {
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
  if (iterations < 0 || eps_r <= 0.0f || omega < 0.0f) {
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

  const std::vector<PixelLevelOperator> level_operator =
      build_level_operator(alpha, width, height, stride, eps_r, omega);
  for (int iteration = 0; iteration < iterations; ++iteration) {
    apply_level_operator_rgb_pass(
        image_red, image_green, image_blue,
        width, height, stride, level_operator,
        fg_red_out, fg_green_out, fg_blue_out,
        bg_red_out, bg_green_out, bg_blue_out);
  }
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
