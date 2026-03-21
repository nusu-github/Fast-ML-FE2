#include "fastmlfe2_ffi.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>

#include <opencv2/core/mat.hpp>
#include <opencv2/imgproc.hpp>

namespace {

constexpr std::array<std::pair<int, int>, 8> kEightOffsets{{
    {-1, -1}, {-1, 0}, {-1, 1}, {0, -1},
    {0, 1},   {1, -1}, {1, 0},  {1, 1},
}};

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

int choose_interpolation(int src_w, int src_h, int dst_w, int dst_h) {
  if (dst_w < src_w || dst_h < src_h) {
    return cv::INTER_AREA;
  }
  return cv::INTER_LINEAR;
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
  cv::resize(src_mat, dst_mat, cv::Size(dst_w, dst_h), 0.0, 0.0,
             choose_interpolation(src_w, src_h, dst_w, dst_h));
  return FASTMLFE2_STATUS_OK;
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

  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const float image_center = load_at(image, stride, x, y);
      const float alpha_center = load_at(alpha, stride, x, y);
      const float beta_center = 1.0f - alpha_center;

      float s = 0.0f;
      float p_f = 0.0f;
      float p_b = 0.0f;

      for (const auto &[dy, dx] : kEightOffsets) {
        const int nx = clamp_index(x + dx, width);
        const int ny = clamp_index(y + dy, height);
        const float alpha_neighbor = load_at(alpha, stride, nx, ny);
        const float weight =
            eps_r + omega * std::fabs(alpha_center - alpha_neighbor);
        s += weight;
        p_f += weight * load_at(fg, stride, nx, ny);
        p_b += weight * load_at(bg, stride, nx, ny);
      }

      const float a2 = alpha_center * alpha_center;
      const float b2 = beta_center * beta_center;
      const float cross = alpha_center * beta_center;
      const float denom = s * (s + a2 + b2);

      const float rhs_f = alpha_center * image_center + p_f;
      const float rhs_b = beta_center * image_center + p_b;
      const float fg_value = ((b2 + s) * rhs_f - cross * rhs_b) / denom;
      const float bg_value = ((a2 + s) * rhs_b - cross * rhs_f) / denom;

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
