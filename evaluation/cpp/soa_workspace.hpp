#pragma once

#include <vector>

struct FloatWorkspace {
  std::vector<float> previous_foreground_storage;
  std::vector<float> previous_background_storage;
  std::vector<float> current_foreground_storage;
  std::vector<float> current_background_storage;
  std::vector<float> image;
  std::vector<float> alpha;
  std::vector<float> neighbor_weights;
  std::vector<float> inverse_weight_sum;
  std::vector<float> inverse_weight_sum_plus_one;
  std::vector<float> foreground_gain;
  std::vector<float> background_gain;
  std::vector<std::int32_t> x_index_map;
  std::vector<std::int32_t> y_index_map;

  void ensure_capacity(std::size_t max_pixels, int max_width, int max_height) {
    previous_foreground_storage.resize(max_pixels * 3);
    previous_background_storage.resize(max_pixels * 3);
    current_foreground_storage.resize(max_pixels * 3);
    current_background_storage.resize(max_pixels * 3);
    image.resize(max_pixels * 3);
    alpha.resize(max_pixels);
    neighbor_weights.resize(max_pixels * 4);
    inverse_weight_sum.resize(max_pixels);
    inverse_weight_sum_plus_one.resize(max_pixels);
    foreground_gain.resize(max_pixels);
    background_gain.resize(max_pixels);
    x_index_map.resize(static_cast<std::size_t>(max_width));
    y_index_map.resize(static_cast<std::size_t>(max_height));
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
