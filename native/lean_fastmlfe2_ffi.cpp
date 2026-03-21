#include <lean/lean.h>

#include <cstdint>
#include <cstring>
#include <string>
#include <utility>
#include <vector>

#include "fastmlfe2_ffi.h"

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

extern "C" lean_obj_res lean_fastmlfe2_gray_image_paper_refine_pass(
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
    return user_error("NativeGrayImage.paperRefinePass: all images must have matching dimensions");
  }

  auto * fg_out = new GrayImageHandle{
      image->width, image->height, image->stride, std::vector<float>(pixel_count(*image))};
  auto * bg_out = new GrayImageHandle{
      image->width, image->height, image->stride, std::vector<float>(pixel_count(*image))};
  const int rc = fastmlfe2_paper_refine_gray_pass(
      image->data.data(), alpha->data.data(), fg->data.data(), bg->data.data(),
      fg_out->data.data(), bg_out->data.data(),
      image->width, image->height, image->stride,
      static_cast<float>(eps_r),
      static_cast<float>(omega));
  if (rc != FASTMLFE2_STATUS_OK) {
    delete fg_out;
    delete bg_out;
    return status_error("NativeGrayImage.paperRefinePass", rc);
  }

  return ok(mk_pair(
      lean_alloc_external(get_gray_image_class(), fg_out),
      lean_alloc_external(get_gray_image_class(), bg_out)));
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
