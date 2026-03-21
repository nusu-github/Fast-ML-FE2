#include "fastmlfe2_ffi.h"

#include <vector>

int main() {
  constexpr int width = 2;
  constexpr int height = 2;
  constexpr int stride = 2;

  std::vector<float> image(width * height, 0.5f);
  std::vector<float> alpha(width * height, 0.5f);
  std::vector<float> fg(width * height, 0.25f);
  std::vector<float> bg(width * height, 0.75f);
  std::vector<float> fgOut(width * height, 0.0f);
  std::vector<float> bgOut(width * height, 0.0f);

  int rc = fastmlfe2_paper_refine_gray_pass(
      image.data(), alpha.data(), fg.data(), bg.data(),
      fgOut.data(), bgOut.data(),
      width, height, stride, 1e-3f, 1.0f);
  if (rc != 0) {
    return rc;
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
