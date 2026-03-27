#pragma once

#include "common.hpp"

#include <vector>

struct LevelStateScratch {
  std::vector<float> previous_foreground;
  std::vector<float> previous_background;
  std::vector<float> current_foreground;
  std::vector<float> current_background;

  void ensure_pixel_capacity(std::size_t max_pixels) {
    previous_foreground.resize(max_pixels * kChannels);
    previous_background.resize(max_pixels * kChannels);
    current_foreground.resize(max_pixels * kChannels);
    current_background.resize(max_pixels * kChannels);
  }
};

struct LevelInputScratch {
  std::vector<float> image;
  std::vector<float> alpha;

  void ensure_pixel_capacity(std::size_t max_pixels) {
    image.resize(max_pixels * kChannels);
    alpha.resize(max_pixels);
  }
};

struct CoefficientScratch {
  std::vector<float> neighbor_weights;
  std::vector<float> inverse_weight_sum;
  std::vector<float> inverse_weight_sum_plus_one;
  std::vector<float> foreground_gain;
  std::vector<float> background_gain;

  void ensure_pixel_capacity(std::size_t max_pixels) {
    neighbor_weights.resize(max_pixels * kNeighborCount);
    inverse_weight_sum.resize(max_pixels);
    inverse_weight_sum_plus_one.resize(max_pixels);
    foreground_gain.resize(max_pixels);
    background_gain.resize(max_pixels);
  }
};

struct FloatWorkspace {
  LevelStateScratch state;
  LevelInputScratch input;
  CoefficientScratch coeff;

  void ensure_pixel_capacity(std::size_t max_pixels) {
    state.ensure_pixel_capacity(max_pixels);
    input.ensure_pixel_capacity(max_pixels);
    coeff.ensure_pixel_capacity(max_pixels);
  }
};

constinit inline thread_local FloatWorkspace *g_thread_workspace = nullptr;

inline FloatWorkspace &thread_workspace() {
  thread_local FloatWorkspace workspace_storage;
  if (g_thread_workspace == nullptr) {
    g_thread_workspace = &workspace_storage;
  }
  return *g_thread_workspace;
}
