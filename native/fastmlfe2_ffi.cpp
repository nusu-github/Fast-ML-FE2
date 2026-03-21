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

struct PixelPrecomputed {
  std::array<std::size_t, 4> neighbor_indices{};
  std::array<float, 4> weights{};
  float total_weight = 0.0f;
  fastmlfe2_precomputed_coeffs coeffs{};
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

fastmlfe2_precomputed_coeffs precompute_coeffs(float alpha, float total_weight) {
  const float beta = 1.0f - alpha;
  const float level_denom = total_weight + alpha * alpha + beta * beta;
  return {
      .image_coeff_fg = alpha / level_denom,
      .image_coeff_bg = beta / level_denom,
      .mean_fg_coeff_fg = (beta * beta + total_weight) / level_denom,
      .mean_bg_coeff_fg = -(alpha * beta) / level_denom,
      .mean_fg_coeff_bg = -(alpha * beta) / level_denom,
      .mean_bg_coeff_bg = (alpha * alpha + total_weight) / level_denom,
  };
}

fastmlfe2_refine_result apply_precomputed_coeffs(
    const fastmlfe2_precomputed_coeffs &coeffs,
    float image,
    float fg_mean,
    float bg_mean) {
  return {
      .fg = coeffs.image_coeff_fg * image +
            coeffs.mean_fg_coeff_fg * fg_mean +
            coeffs.mean_bg_coeff_fg * bg_mean,
      .bg = coeffs.image_coeff_bg * image +
            coeffs.mean_fg_coeff_bg * fg_mean +
            coeffs.mean_bg_coeff_bg * bg_mean,
  };
}

PixelPrecomputed precompute_pixel(
    const float *alpha,
    int width,
    int height,
    int stride,
    int x,
    int y,
    float eps_r,
    float omega) {
  PixelPrecomputed pixel;
  const float alpha_center = load_at(alpha, stride, x, y);

  for (std::size_t i = 0; i < kFourOffsets.size(); ++i) {
    const auto &[dy, dx] = kFourOffsets[i];
    const int nx = clamp_index(x + dx, width);
    const int ny = clamp_index(y + dy, height);
    const float alpha_neighbor = load_at(alpha, stride, nx, ny);
    const float weight =
        eps_r + omega * std::fabs(alpha_center - alpha_neighbor);
    pixel.neighbor_indices[i] = flat_index(stride, nx, ny);
    pixel.weights[i] = weight;
    pixel.total_weight += weight;
  }

  pixel.coeffs = precompute_coeffs(alpha_center, pixel.total_weight);
  return pixel;
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

extern "C" fastmlfe2_precomputed_coeffs fastmlfe2_debug_precompute_coeffs(
    float alpha,
    float total_weight) {
  return precompute_coeffs(alpha, total_weight);
}

extern "C" fastmlfe2_refine_result fastmlfe2_debug_apply_precomputed_coeffs(
    fastmlfe2_precomputed_coeffs coeffs,
    float image,
    float fg_mean,
    float bg_mean) {
  return apply_precomputed_coeffs(coeffs, image, fg_mean, bg_mean);
}

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

extern "C" int fastmlfe2_paper_refine_gray_pass(
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
  if (overlaps(fg, fg_out, count) || overlaps(fg, bg_out, count) ||
      overlaps(bg, fg_out, count) || overlaps(bg, bg_out, count)) {
    return FASTMLFE2_STATUS_ALIASING;
  }

  std::copy(fg, fg + count, fg_out);
  std::copy(bg, bg + count, bg_out);

  std::vector<PixelPrecomputed> precomputed(
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height));

  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      precomputed[static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
                  static_cast<std::size_t>(x)] =
          precompute_pixel(alpha, width, height, stride, x, y, eps_r, omega);
    }
  }

  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const float image_center = load_at(image, stride, x, y);
      const PixelPrecomputed &pixel =
          precomputed[static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
                      static_cast<std::size_t>(x)];

      float p_f = 0.0f;
      float p_b = 0.0f;

      for (std::size_t i = 0; i < pixel.neighbor_indices.size(); ++i) {
        const std::size_t idx = pixel.neighbor_indices[i];
        const float weight = pixel.weights[i];
        p_f += weight * fg_out[idx];
        p_b += weight * bg_out[idx];
      }

      const float fg_mean = p_f / pixel.total_weight;
      const float bg_mean = p_b / pixel.total_weight;
      const fastmlfe2_refine_result result =
          apply_precomputed_coeffs(pixel.coeffs, image_center, fg_mean, bg_mean);
      const float fg_value = std::clamp(result.fg, 0.0f, 1.0f);
      const float bg_value = std::clamp(result.bg, 0.0f, 1.0f);

      store_at(fg_out, stride, x, y, fg_value);
      store_at(bg_out, stride, x, y, bg_value);
    }
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
