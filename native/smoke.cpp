#include "fastmlfe2_ffi.h"

#include <cmath>
#include <cstdlib>
#include <vector>

namespace {

bool approx_eq(float lhs, float rhs, float eps = 1.0e-5f) {
  return std::fabs(lhs - rhs) <= eps;
}

void expect(bool condition, int rc) {
  if (!condition) {
    std::exit(rc);
  }
}

void expect_vec(const std::vector<float> &actual, const std::vector<float> &expected, int rc) {
  expect(actual.size() == expected.size(), rc);
  for (std::size_t i = 0; i < actual.size(); ++i) {
    if (!approx_eq(actual[i], expected[i])) {
      std::exit(rc);
    }
  }
}

}

int main() {
  {
    constexpr int width = 1;
    constexpr int height = 1;
    constexpr int stride = 1;

    std::vector<float> image{0.3f};
    std::vector<float> alpha{0.25f};
    std::vector<float> fg{0.8f};
    std::vector<float> bg{0.1f};
    std::vector<float> fgOut(width * height, 0.0f);
    std::vector<float> bgOut(width * height, 0.0f);

    int rc = fastmlfe2_reference_refine_gray_single_pass(
        image.data(), alpha.data(), fg.data(), bg.data(),
        fgOut.data(), bgOut.data(),
        width, height, stride, 0.5f, 1.0f);
    if (rc != 0) {
      return rc;
    }
    expect(approx_eq(fgOut[0], 0.8023809524f), 12);
    expect(approx_eq(bgOut[0], 0.1071428571f), 13);
  }

  constexpr int width = 2;
  constexpr int height = 1;
  constexpr int stride = 2;

  std::vector<float> image{0.2f, 0.8f};
  std::vector<float> alpha{0.2f, 0.8f};
  std::vector<float> fg{1.0f, 0.0f};
  std::vector<float> bg{0.0f, 1.0f};
  std::vector<float> fgOut(width * height, 0.0f);
  std::vector<float> bgOut(width * height, 0.0f);

  int rc = fastmlfe2_reference_refine_gray_single_pass(
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

  rc = fastmlfe2_reference_refine_gray_single_pass(
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

  {
    constexpr int rgbWidth = 2;
    constexpr int rgbHeight = 2;
    constexpr int rgbStride = 2;
    std::vector<float> imageRed{0.1f, 0.4f, 0.7f, 0.9f};
    std::vector<float> imageGreen{0.2f, 0.6f, 0.3f, 0.8f};
    std::vector<float> imageBlue{0.9f, 0.5f, 0.2f, 0.1f};
    std::vector<float> alphaRgb{0.0f, 0.3f, 0.8f, 1.0f};
    std::vector<float> fgRed{0.2f, 0.2f, 0.8f, 0.8f};
    std::vector<float> fgGreen{0.1f, 0.3f, 0.7f, 0.9f};
    std::vector<float> fgBlue{0.8f, 0.6f, 0.4f, 0.2f};
    std::vector<float> bgRed{0.0f, 0.1f, 0.4f, 0.5f};
    std::vector<float> bgGreen{0.9f, 0.7f, 0.3f, 0.1f};
    std::vector<float> bgBlue{0.2f, 0.4f, 0.6f, 0.8f};
    std::vector<float> fgRedOut(4), fgGreenOut(4), fgBlueOut(4);
    std::vector<float> bgRedOut(4), bgGreenOut(4), bgBlueOut(4);

    rc = fastmlfe2_reference_refine_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedOut.data(), fgGreenOut.data(), fgBlueOut.data(),
        bgRedOut.data(), bgGreenOut.data(), bgBlueOut.data(),
        rgbWidth, rgbHeight, rgbStride, 3, 5e-3f, 1e-1f);
    if (rc != 0) {
      return rc;
    }

    expect_vec(fgRedOut, {0.811771f, 0.864838f, 0.837793f, 0.896152f}, 14);
    expect_vec(fgGreenOut, {0.49459f, 0.766521f, 0.360411f, 0.787745f}, 15);
    expect_vec(fgBlueOut, {0.0904351f, 0.0740971f, 0.0498697f, 0.0971273f}, 16);
    expect_vec(bgRedOut, {0.110297f, 0.199114f, 0.142401f, 0.188636f}, 17);
    expect_vec(bgGreenOut, {0.206804f, 0.492881f, 0.19722f, 0.416796f}, 18);
    expect_vec(bgBlueOut, {0.885632f, 0.696953f, 0.831104f, 0.728247f}, 19);
  }

  return fastmlfe2_resize_float_gray(
      image.data(), width, height, stride,
      fgOut.data(), width, height, stride);
}
