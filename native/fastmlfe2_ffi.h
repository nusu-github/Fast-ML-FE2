#ifndef FASTMLFE2_FFI_H
#define FASTMLFE2_FFI_H

#ifdef __cplusplus
extern "C" {
#endif

enum fastmlfe2_status {
  FASTMLFE2_STATUS_OK = 0,
  FASTMLFE2_STATUS_NULL_POINTER = 1,
  FASTMLFE2_STATUS_INVALID_DIMENSIONS = 2,
  FASTMLFE2_STATUS_INVALID_STRIDE = 3,
  FASTMLFE2_STATUS_INVALID_PARAMS = 4,
  FASTMLFE2_STATUS_ALIASING = 5
};

int fastmlfe2_resize_float_gray(
    const float *src,
    int src_w,
    int src_h,
    int src_stride,
    float *dst,
    int dst_w,
    int dst_h,
    int dst_stride);

int fastmlfe2_resize_float_gray_nearest(
    const float *src,
    int src_w,
    int src_h,
    int src_stride,
    float *dst,
    int dst_w,
    int dst_h,
    int dst_stride);

int fastmlfe2_reference_refine_gray_single_pass(
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
    float omega);

int fastmlfe2_reference_refine_rgb(
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
    float update_tol);

int fastmlfe2_global_spd_vcycle_rgb(
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
    float residual_tol);

int fastmlfe2_clamp01_gray(float *buf, int width, int height, int stride);

#ifdef __cplusplus
}
#endif

#endif
