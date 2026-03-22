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
        rgbWidth, rgbHeight, rgbStride, 3, 5e-3f, 1e-1f, 0.0f, 0.0f);
    if (rc != 0) {
      return rc;
    }

    expect_vec(fgRedOut, {0.830597758f, 0.88038969f, 0.843004763f, 0.894744515f}, 14);
    expect_vec(fgGreenOut, {0.461264521f, 0.739589155f, 0.351412773f, 0.784993887f}, 15);
    expect_vec(fgBlueOut, {0.102423653f, 0.0851337761f, 0.0536182709f, 0.10242942f}, 16);
    expect_vec(bgRedOut, {0.107164577f, 0.189354777f, 0.128722265f, 0.194471642f}, 17);
    expect_vec(bgGreenOut, {0.212035656f, 0.509556174f, 0.220379204f, 0.447383642f}, 18);
    expect_vec(bgBlueOut, {0.883042753f, 0.689597011f, 0.820391357f, 0.680520773f}, 19);

    std::vector<float> fgRedOne(4), fgGreenOne(4), fgBlueOne(4);
    std::vector<float> bgRedOne(4), bgGreenOne(4), bgBlueOne(4);
    rc = fastmlfe2_reference_refine_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedOne.data(), fgGreenOne.data(), fgBlueOne.data(),
        bgRedOne.data(), bgGreenOne.data(), bgBlueOne.data(),
        rgbWidth, rgbHeight, rgbStride, 1, 5e-3f, 1e-1f, 0.0f, 0.0f);
    if (rc != 0) {
      return rc;
    }

    std::vector<float> fgRedResidual(4), fgGreenResidual(4), fgBlueResidual(4);
    std::vector<float> bgRedResidual(4), bgGreenResidual(4), bgBlueResidual(4);
    rc = fastmlfe2_reference_refine_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedResidual.data(), fgGreenResidual.data(), fgBlueResidual.data(),
        bgRedResidual.data(), bgGreenResidual.data(), bgBlueResidual.data(),
        rgbWidth, rgbHeight, rgbStride, 5, 5e-3f, 1e-1f, 100.0f, 0.0f);
    if (rc != 0) {
      return rc;
    }
    expect_vec(fgRedResidual, fgRedOne, 20);
    expect_vec(fgGreenResidual, fgGreenOne, 21);
    expect_vec(fgBlueResidual, fgBlueOne, 22);
    expect_vec(bgRedResidual, bgRedOne, 23);
    expect_vec(bgGreenResidual, bgGreenOne, 24);
    expect_vec(bgBlueResidual, bgBlueOne, 25);

    std::vector<float> fgRedUpdate(4), fgGreenUpdate(4), fgBlueUpdate(4);
    std::vector<float> bgRedUpdate(4), bgGreenUpdate(4), bgBlueUpdate(4);
    rc = fastmlfe2_reference_refine_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedUpdate.data(), fgGreenUpdate.data(), fgBlueUpdate.data(),
        bgRedUpdate.data(), bgGreenUpdate.data(), bgBlueUpdate.data(),
        rgbWidth, rgbHeight, rgbStride, 5, 5e-3f, 1e-1f, 0.0f, 100.0f);
    if (rc != 0) {
      return rc;
    }
    expect_vec(fgRedUpdate, fgRedOne, 26);
    expect_vec(fgGreenUpdate, fgGreenOne, 27);
    expect_vec(fgBlueUpdate, fgBlueOne, 28);
    expect_vec(bgRedUpdate, bgRedOne, 29);
    expect_vec(bgGreenUpdate, bgGreenOne, 30);
    expect_vec(bgBlueUpdate, bgBlueOne, 31);

    std::vector<float> fgRedVcycleZero(4), fgGreenVcycleZero(4), fgBlueVcycleZero(4);
    std::vector<float> bgRedVcycleZero(4), bgGreenVcycleZero(4), bgBlueVcycleZero(4);
    rc = fastmlfe2_global_spd_vcycle_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedVcycleZero.data(), fgGreenVcycleZero.data(), fgBlueVcycleZero.data(),
        bgRedVcycleZero.data(), bgGreenVcycleZero.data(), bgBlueVcycleZero.data(),
        rgbWidth, rgbHeight, rgbStride, 2, 0, 1, 1, 4, 5e-3f, 1e-1f, 0.0f);
    if (rc != 0) {
      return rc;
    }
    expect_vec(fgRedVcycleZero, fgRed, 32);
    expect_vec(fgGreenVcycleZero, fgGreen, 33);
    expect_vec(fgBlueVcycleZero, fgBlue, 34);
    expect_vec(bgRedVcycleZero, bgRed, 35);
    expect_vec(bgGreenVcycleZero, bgGreen, 36);
    expect_vec(bgBlueVcycleZero, bgBlue, 37);

    std::vector<float> fgRedVcycle(4), fgGreenVcycle(4), fgBlueVcycle(4);
    std::vector<float> bgRedVcycle(4), bgGreenVcycle(4), bgBlueVcycle(4);
    rc = fastmlfe2_global_spd_vcycle_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedVcycle.data(), fgGreenVcycle.data(), fgBlueVcycle.data(),
        bgRedVcycle.data(), bgGreenVcycle.data(), bgBlueVcycle.data(),
        rgbWidth, rgbHeight, rgbStride, 2, 1, 1, 1, 4, 5e-3f, 1e-1f, 0.0f);
    if (rc != 0) {
      return rc;
    }
    expect_vec(fgRedVcycle, {0.807818f, 0.873886f, 0.839679f, 0.891312f}, 38);
    expect_vec(fgGreenVcycle, {0.467442f, 0.74083f, 0.352024f, 0.785147f}, 39);
    expect_vec(fgBlueVcycle, {0.158402f, 0.110178f, 0.0641333f, 0.110752f}, 40);
    expect_vec(bgRedVcycle, {0.108411f, 0.192118f, 0.132425f, 0.199902f}, 41);
    expect_vec(bgGreenVcycle, {0.212984f, 0.509907f, 0.220897f, 0.45419f}, 42);
    expect_vec(bgBlueVcycle, {0.876525f, 0.675309f, 0.800832f, 0.63526f}, 43);

    std::vector<float> fgRedVcycleStop(4), fgGreenVcycleStop(4), fgBlueVcycleStop(4);
    std::vector<float> bgRedVcycleStop(4), bgGreenVcycleStop(4), bgBlueVcycleStop(4);
    rc = fastmlfe2_global_spd_vcycle_rgb(
        imageRed.data(), imageGreen.data(), imageBlue.data(), alphaRgb.data(),
        fgRed.data(), fgGreen.data(), fgBlue.data(),
        bgRed.data(), bgGreen.data(), bgBlue.data(),
        fgRedVcycleStop.data(), fgGreenVcycleStop.data(), fgBlueVcycleStop.data(),
        bgRedVcycleStop.data(), bgGreenVcycleStop.data(), bgBlueVcycleStop.data(),
        rgbWidth, rgbHeight, rgbStride, 2, 5, 1, 1, 4, 5e-3f, 1e-1f, 100.0f);
    if (rc != 0) {
      return rc;
    }
    expect_vec(fgRedVcycleStop, fgRedVcycle, 44);
    expect_vec(fgGreenVcycleStop, fgGreenVcycle, 45);
    expect_vec(fgBlueVcycleStop, fgBlueVcycle, 46);
    expect_vec(bgRedVcycleStop, bgRedVcycle, 47);
    expect_vec(bgGreenVcycleStop, bgGreenVcycle, 48);
    expect_vec(bgBlueVcycleStop, bgBlueVcycle, 49);
  }

  return fastmlfe2_resize_float_gray(
      image.data(), width, height, stride,
      fgOut.data(), width, height, stride);
}
