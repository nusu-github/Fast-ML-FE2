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

int fastmlfe2_paper_refine_gray_pass(
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

int fastmlfe2_clamp01_gray(float *buf, int width, int height, int stride);

#ifdef __cplusplus
}
#endif

#endif
