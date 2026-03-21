#include "fastmlfe2_ffi.h"

#include <cmath>
#include <vector>

namespace {

bool approx_eq(float lhs, float rhs, float eps = 1.0e-5f) {
  return std::fabs(lhs - rhs) <= eps;
}

}

int main() {
  constexpr int width = 2;
  constexpr int height = 1;
  constexpr int stride = 2;

  std::vector<float> image{0.2f, 0.8f};
  std::vector<float> alpha{0.2f, 0.8f};
  std::vector<float> fg{1.0f, 0.0f};
  std::vector<float> bg{0.0f, 1.0f};
  std::vector<float> fgOut(width * height, 0.0f);
  std::vector<float> bgOut(width * height, 0.0f);

  int rc = fastmlfe2_paper_refine_gray_pass(
      image.data(), alpha.data(), fg.data(), bg.data(),
      fgOut.data(), bgOut.data(),
      width, height, stride, 5e-3f, 1e-1f);
  if (rc != 0) {
    return rc;
  }

  if (!approx_eq(fgOut[0], 0.0592105263f) ||
      !approx_eq(bgOut[0], 0.2993421053f) ||
      !approx_eq(fgOut[1], 0.7590244114f) ||
      !approx_eq(bgOut[1], 0.6084444252f)) {
    return 10;
  }

  image = {0.79610804f, 0.97879037f};
  alpha = {0.15680273f, 0.45511161f};
  fg = {1.3971344f, 1.4847438f};
  bg = {-0.3239145f, 1.6373175f};
  std::fill(fgOut.begin(), fgOut.end(), 0.0f);
  std::fill(bgOut.begin(), bgOut.end(), 0.0f);

  rc = fastmlfe2_paper_refine_gray_pass(
      image.data(), alpha.data(), fg.data(), bg.data(),
      fgOut.data(), bgOut.data(),
      width, height, stride, 5e-3f, 1e-1f);
  if (rc != 0) {
    return rc;
  }

  if (!approx_eq(fgOut[0], 1.0f) ||
      !approx_eq(bgOut[0], 0.70838916f) ||
      !approx_eq(fgOut[1], 1.0f) ||
      !approx_eq(bgOut[1], 0.90824038f)) {
    return 11;
  }

  rc = fastmlfe2_clamp01_gray(fgOut.data(), width, height, stride);
  if (rc != 0) {
    return rc;
  }

  rc = fastmlfe2_clamp01_gray(bgOut.data(), width, height, stride);
  if (rc != 0) {
    return rc;
  }

  return fastmlfe2_resize_float_gray(
      image.data(), width, height, stride,
      fgOut.data(), width, height, stride);
}
