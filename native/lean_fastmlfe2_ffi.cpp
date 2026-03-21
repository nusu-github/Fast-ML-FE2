#include <lean/lean.h>

#include <cstdint>
#include <cstring>
#include <string>
#include <utility>
#include <vector>

#include "fastmlfe2_ffi.h"
#include <opencv2/imgcodecs.hpp>

namespace {

struct GrayImageHandle {
  int width;
  int height;
  int stride;
  std::vector<float> data;
};

lean_external_class * g_gray_image_class = nullptr;

void gray_image_finalize(void * ptr) {
  delete static_cast<GrayImageHandle *>(ptr);
}

void gray_image_foreach([[maybe_unused]] void * ptr, [[maybe_unused]] b_lean_obj_arg f) {}

lean_external_class * get_gray_image_class() {
  if (g_gray_image_class == nullptr) {
    g_gray_image_class = lean_register_external_class(gray_image_finalize, gray_image_foreach);
  }
  return g_gray_image_class;
}

GrayImageHandle * get_handle(b_lean_obj_arg obj) {
  return static_cast<GrayImageHandle *>(lean_get_external_data(obj));
}

lean_obj_res ok(lean_obj_arg value) {
  return lean_io_result_mk_ok(value);
}

lean_obj_res user_error(const std::string & message) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message.c_str())));
}

lean_obj_res status_error(const char * fn, int status) {
  switch (status) {
    case FASTMLFE2_STATUS_NULL_POINTER:
      return user_error(std::string(fn) + ": null pointer");
    case FASTMLFE2_STATUS_INVALID_DIMENSIONS:
      return user_error(std::string(fn) + ": invalid dimensions");
    case FASTMLFE2_STATUS_INVALID_STRIDE:
      return user_error(std::string(fn) + ": invalid stride");
    case FASTMLFE2_STATUS_INVALID_PARAMS:
      return user_error(std::string(fn) + ": invalid parameters");
    case FASTMLFE2_STATUS_ALIASING:
      return user_error(std::string(fn) + ": aliasing detected");
    default:
      return user_error(std::string(fn) + ": unknown native error");
  }
}

std::size_t pixel_count(const GrayImageHandle & image) {
  return static_cast<std::size_t>(image.width) * static_cast<std::size_t>(image.height);
}

bool same_dims(const GrayImageHandle & lhs, const GrayImageHandle & rhs) {
  return lhs.width == rhs.width && lhs.height == rhs.height;
}

lean_obj_res copy_to_float_array(const GrayImageHandle & image) {
  lean_object * arr = lean_mk_empty_array_with_capacity(lean_box(pixel_count(image)));
  lean_object * floats = lean_float_array_mk(arr);
  for (float value : image.data) {
    floats = lean_float_array_push(floats, static_cast<double>(value));
  }
  return floats;
}

lean_obj_res mk_pair(lean_obj_arg fst, lean_obj_arg snd) {
  lean_object * pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, fst);
  lean_ctor_set(pair, 1, snd);
  return pair;
}

lean_obj_res mk_gray_triple(lean_obj_arg first, lean_obj_arg second, lean_obj_arg third) {
  return mk_pair(first, mk_pair(second, third));
}

GrayImageHandle * alloc_image(int width, int height) {
  return new GrayImageHandle{
      width,
      height,
      width,
      std::vector<float>(static_cast<std::size_t>(width) * static_cast<std::size_t>(height))};
}

cv::Mat to_gray_8u(const GrayImageHandle & image) {
  cv::Mat out(image.height, image.width, CV_8UC1);
  for (int y = 0; y < image.height; ++y) {
    for (int x = 0; x < image.width; ++x) {
      const auto idx =
          static_cast<std::size_t>(y) * static_cast<std::size_t>(image.stride) + static_cast<std::size_t>(x);
      const float clamped = std::clamp(image.data[idx], 0.0f, 1.0f);
      out.at<unsigned char>(y, x) = static_cast<unsigned char>(clamped * 255.0f + 0.5f);
    }
  }
  return out;
}

}  // namespace

extern "C" lean_obj_res lean_fastmlfe2_gray_image_of_float_array(
    uint32_t width_u32,
    uint32_t height_u32,
    b_lean_obj_arg data_obj) {
  if (width_u32 == 0 || height_u32 == 0) {
    return user_error("NativeGrayImage.ofFloatArray: dimensions must be positive");
  }
  const std::size_t width = width_u32;
  const std::size_t height = height_u32;
  const std::size_t expected = width * height;
  const std::size_t actual = lean_unbox(lean_float_array_size(data_obj));
  if (actual != expected) {
    return user_error(
        "NativeGrayImage.ofFloatArray: data length must equal width * height "
        "(expected " + std::to_string(expected) + ", got " + std::to_string(actual) + ")");
  }

  auto * handle = new GrayImageHandle{
      static_cast<int>(width_u32),
      static_cast<int>(height_u32),
      static_cast<int>(width_u32),
      std::vector<float>(expected)};
  for (std::size_t i = 0; i < expected; ++i) {
    handle->data[i] = static_cast<float>(lean_float_array_uget(data_obj, i));
  }
  return ok(lean_alloc_external(get_gray_image_class(), handle));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_to_float_array(
    b_lean_obj_arg image_obj) {
  return ok(copy_to_float_array(*get_handle(image_obj)));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_width(
    b_lean_obj_arg image_obj) {
  return ok(lean_box_uint32(static_cast<uint32_t>(get_handle(image_obj)->width)));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_height(
    b_lean_obj_arg image_obj) {
  return ok(lean_box_uint32(static_cast<uint32_t>(get_handle(image_obj)->height)));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_resize(
    b_lean_obj_arg image_obj,
    uint32_t width_u32,
    uint32_t height_u32) {
  if (width_u32 == 0 || height_u32 == 0) {
    return user_error("NativeGrayImage.resize: dimensions must be positive");
  }

  const auto * image = get_handle(image_obj);
  auto * out = new GrayImageHandle{
      static_cast<int>(width_u32),
      static_cast<int>(height_u32),
      static_cast<int>(width_u32),
      std::vector<float>(static_cast<std::size_t>(width_u32) * static_cast<std::size_t>(height_u32))};
  const int rc = fastmlfe2_resize_float_gray(
      image->data.data(), image->width, image->height, image->stride,
      out->data.data(), out->width, out->height, out->stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    delete out;
    return status_error("NativeGrayImage.resize", rc);
  }
  return ok(lean_alloc_external(get_gray_image_class(), out));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_resize_nearest(
    b_lean_obj_arg image_obj,
    uint32_t width_u32,
    uint32_t height_u32) {
  if (width_u32 == 0 || height_u32 == 0) {
    return user_error("NativeGrayImage.resizeNearest: dimensions must be positive");
  }

  const auto * image = get_handle(image_obj);
  auto * out = new GrayImageHandle{
      static_cast<int>(width_u32),
      static_cast<int>(height_u32),
      static_cast<int>(width_u32),
      std::vector<float>(static_cast<std::size_t>(width_u32) * static_cast<std::size_t>(height_u32))};
  const int rc = fastmlfe2_resize_float_gray_nearest(
      image->data.data(), image->width, image->height, image->stride,
      out->data.data(), out->width, out->height, out->stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    delete out;
    return status_error("NativeGrayImage.resizeNearest", rc);
  }
  return ok(lean_alloc_external(get_gray_image_class(), out));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_reference_refine_single_pass(
    b_lean_obj_arg image_obj,
    b_lean_obj_arg alpha_obj,
    b_lean_obj_arg fg_obj,
    b_lean_obj_arg bg_obj,
    double eps_r,
    double omega) {
  const auto * image = get_handle(image_obj);
  const auto * alpha = get_handle(alpha_obj);
  const auto * fg = get_handle(fg_obj);
  const auto * bg = get_handle(bg_obj);
  if (!same_dims(*image, *alpha) || !same_dims(*image, *fg) || !same_dims(*image, *bg)) {
    return user_error(
        "NativeGrayImage.referenceRefineSinglePass: all images must have matching dimensions");
  }

  auto * fg_out = new GrayImageHandle{
      image->width, image->height, image->stride, std::vector<float>(pixel_count(*image))};
  auto * bg_out = new GrayImageHandle{
      image->width, image->height, image->stride, std::vector<float>(pixel_count(*image))};
  const int rc = fastmlfe2_reference_refine_gray_single_pass(
      image->data.data(), alpha->data.data(), fg->data.data(), bg->data.data(),
      fg_out->data.data(), bg_out->data.data(),
      image->width, image->height, image->stride,
      static_cast<float>(eps_r),
      static_cast<float>(omega));
  if (rc != FASTMLFE2_STATUS_OK) {
    delete fg_out;
    delete bg_out;
    return status_error("NativeGrayImage.referenceRefineSinglePass", rc);
  }

  return ok(mk_pair(
      lean_alloc_external(get_gray_image_class(), fg_out),
      lean_alloc_external(get_gray_image_class(), bg_out)));
}

extern "C" lean_obj_res lean_fastmlfe2_rgb_image_reference_refine(
    b_lean_obj_arg image_red_obj,
    b_lean_obj_arg image_green_obj,
    b_lean_obj_arg image_blue_obj,
    b_lean_obj_arg alpha_obj,
    b_lean_obj_arg fg_red_obj,
    b_lean_obj_arg fg_green_obj,
    b_lean_obj_arg fg_blue_obj,
    b_lean_obj_arg bg_red_obj,
    b_lean_obj_arg bg_green_obj,
    b_lean_obj_arg bg_blue_obj,
    uint32_t iterations,
    double eps_r,
    double omega) {
  const auto * image_red = get_handle(image_red_obj);
  const auto * image_green = get_handle(image_green_obj);
  const auto * image_blue = get_handle(image_blue_obj);
  const auto * alpha = get_handle(alpha_obj);
  const auto * fg_red = get_handle(fg_red_obj);
  const auto * fg_green = get_handle(fg_green_obj);
  const auto * fg_blue = get_handle(fg_blue_obj);
  const auto * bg_red = get_handle(bg_red_obj);
  const auto * bg_green = get_handle(bg_green_obj);
  const auto * bg_blue = get_handle(bg_blue_obj);
  if (!same_dims(*image_red, *image_green) || !same_dims(*image_red, *image_blue) ||
      !same_dims(*image_red, *alpha) ||
      !same_dims(*image_red, *fg_red) || !same_dims(*image_red, *fg_green) ||
      !same_dims(*image_red, *fg_blue) ||
      !same_dims(*image_red, *bg_red) || !same_dims(*image_red, *bg_green) ||
      !same_dims(*image_red, *bg_blue)) {
    return user_error("NativeRgbImage.referenceRefine: all images must have matching dimensions");
  }

  auto * fg_red_out = alloc_image(image_red->width, image_red->height);
  auto * fg_green_out = alloc_image(image_red->width, image_red->height);
  auto * fg_blue_out = alloc_image(image_red->width, image_red->height);
  auto * bg_red_out = alloc_image(image_red->width, image_red->height);
  auto * bg_green_out = alloc_image(image_red->width, image_red->height);
  auto * bg_blue_out = alloc_image(image_red->width, image_red->height);
  const int rc = fastmlfe2_reference_refine_rgb(
      image_red->data.data(), image_green->data.data(), image_blue->data.data(),
      alpha->data.data(),
      fg_red->data.data(), fg_green->data.data(), fg_blue->data.data(),
      bg_red->data.data(), bg_green->data.data(), bg_blue->data.data(),
      fg_red_out->data.data(), fg_green_out->data.data(), fg_blue_out->data.data(),
      bg_red_out->data.data(), bg_green_out->data.data(), bg_blue_out->data.data(),
      image_red->width, image_red->height, image_red->stride,
      static_cast<int>(iterations),
      static_cast<float>(eps_r),
      static_cast<float>(omega));
  if (rc != FASTMLFE2_STATUS_OK) {
    delete fg_red_out;
    delete fg_green_out;
    delete fg_blue_out;
    delete bg_red_out;
    delete bg_green_out;
    delete bg_blue_out;
    return status_error("NativeRgbImage.referenceRefine", rc);
  }

  return ok(mk_pair(
      mk_gray_triple(
          lean_alloc_external(get_gray_image_class(), fg_red_out),
          lean_alloc_external(get_gray_image_class(), fg_green_out),
          lean_alloc_external(get_gray_image_class(), fg_blue_out)),
      mk_gray_triple(
          lean_alloc_external(get_gray_image_class(), bg_red_out),
          lean_alloc_external(get_gray_image_class(), bg_green_out),
          lean_alloc_external(get_gray_image_class(), bg_blue_out))));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_clamp01(
    b_lean_obj_arg image_obj) {
  auto * image = get_handle(image_obj);
  const int rc = fastmlfe2_clamp01_gray(image->data.data(), image->width, image->height, image->stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    return status_error("NativeGrayImage.clamp01", rc);
  }
  return ok(lean_box(0));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_read_png_gray(b_lean_obj_arg path_obj) {
  const std::string path = lean_string_cstr(path_obj);
  cv::Mat image = cv::imread(path, cv::IMREAD_GRAYSCALE);
  if (image.empty()) {
    return user_error("NativeGrayImage.readPngGray: failed to read PNG");
  }
  auto * handle = alloc_image(image.cols, image.rows);
  for (int y = 0; y < image.rows; ++y) {
    for (int x = 0; x < image.cols; ++x) {
      handle->data[static_cast<std::size_t>(y) * static_cast<std::size_t>(handle->stride) +
                   static_cast<std::size_t>(x)] =
          static_cast<float>(image.at<unsigned char>(y, x)) / 255.0f;
    }
  }
  return ok(lean_alloc_external(get_gray_image_class(), handle));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_write_png_gray(
    b_lean_obj_arg path_obj,
    b_lean_obj_arg image_obj) {
  const std::string path = lean_string_cstr(path_obj);
  const auto * image = get_handle(image_obj);
  if (!cv::imwrite(path, to_gray_8u(*image))) {
    return user_error("NativeGrayImage.writePngGray: failed to write PNG");
  }
  return ok(lean_box(0));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_read_png_rgb_channel(
    b_lean_obj_arg path_obj,
    uint32_t channel) {
  if (channel > 2) {
    return user_error("NativeGrayImage.readPngRgbChannel: channel must be 0, 1, or 2");
  }
  const std::string path = lean_string_cstr(path_obj);
  cv::Mat image = cv::imread(path, cv::IMREAD_COLOR);
  if (image.empty()) {
    return user_error("NativeGrayImage.readPngRgbChannel: failed to read PNG");
  }
  const int bgr_channel = 2 - static_cast<int>(channel);
  auto * handle = alloc_image(image.cols, image.rows);
  for (int y = 0; y < image.rows; ++y) {
    for (int x = 0; x < image.cols; ++x) {
      const auto pixel = image.at<cv::Vec3b>(y, x);
      handle->data[static_cast<std::size_t>(y) * static_cast<std::size_t>(handle->stride) +
                   static_cast<std::size_t>(x)] =
          static_cast<float>(pixel[bgr_channel]) / 255.0f;
    }
  }
  return ok(lean_alloc_external(get_gray_image_class(), handle));
}

extern "C" lean_obj_res lean_fastmlfe2_gray_image_write_png_rgb(
    b_lean_obj_arg path_obj,
    b_lean_obj_arg red_obj,
    b_lean_obj_arg green_obj,
    b_lean_obj_arg blue_obj) {
  const std::string path = lean_string_cstr(path_obj);
  const auto * red = get_handle(red_obj);
  const auto * green = get_handle(green_obj);
  const auto * blue = get_handle(blue_obj);
  if (!same_dims(*red, *green) || !same_dims(*red, *blue)) {
    return user_error("NativeRgbImage.writePng: RGB channel dimensions must match");
  }

  cv::Mat image(red->height, red->width, CV_8UC3);
  for (int y = 0; y < red->height; ++y) {
    for (int x = 0; x < red->width; ++x) {
      const auto idx =
          static_cast<std::size_t>(y) * static_cast<std::size_t>(red->stride) + static_cast<std::size_t>(x);
      image.at<cv::Vec3b>(y, x) = cv::Vec3b(
          static_cast<unsigned char>(std::clamp(blue->data[idx], 0.0f, 1.0f) * 255.0f + 0.5f),
          static_cast<unsigned char>(std::clamp(green->data[idx], 0.0f, 1.0f) * 255.0f + 0.5f),
          static_cast<unsigned char>(std::clamp(red->data[idx], 0.0f, 1.0f) * 255.0f + 0.5f));
    }
  }

  if (!cv::imwrite(path, image)) {
    return user_error("NativeRgbImage.writePng: failed to write PNG");
  }
  return ok(lean_box(0));
}
