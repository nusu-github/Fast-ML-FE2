#pragma once

#include "solver_float.hpp"

inline void bind_cpu_impl(nb::module_ &m) {
  m.def(
      "estimate_multilevel_foreground_background",
      &estimate_multilevel_foreground_background,
      nb::arg("foreground_out"),
      nb::arg("background_out"),
      nb::arg("input_image"),
      nb::arg("input_alpha"),
      nb::arg("regularization"),
      nb::arg("gradient_weight"),
      nb::arg("n_small_iterations"),
      nb::arg("n_big_iterations"),
      nb::arg("small_size"));
  m.def("_resize_nearest_rgb", &resize_nearest_rgb, nb::arg("dst"), nb::arg("src"));
  m.def("_resize_nearest_scalar", &resize_nearest_scalar, nb::arg("dst"), nb::arg("src"));
  m.def("_build_resize_index_map", &build_resize_index_map, nb::arg("src_size"), nb::arg("dst_size"));
  m.def(
      "_build_level_solver_coefficients",
      &build_level_solver_coefficients,
      nb::arg("alpha"),
      nb::arg("regularization"),
      nb::arg("gradient_weight"),
      nb::arg("neighbor_weights"),
      nb::arg("inverse_weight_sum"),
      nb::arg("inverse_weight_sum_plus_one"),
      nb::arg("foreground_gain"),
      nb::arg("background_gain"));
  m.def(
      "_update_red_black_half_step",
      &update_red_black_half_step,
      nb::arg("foreground"),
      nb::arg("background"),
      nb::arg("image"),
      nb::arg("alpha"),
      nb::arg("neighbor_weights"),
      nb::arg("inverse_weight_sum"),
      nb::arg("inverse_weight_sum_plus_one"),
      nb::arg("foreground_gain"),
      nb::arg("background_gain"),
      nb::arg("h"),
      nb::arg("w"),
      nb::arg("color"));
  m.def(
      "_update_red_black_half_step_from_previous_level",
      &update_red_black_half_step_from_previous_level,
      nb::arg("foreground"),
      nb::arg("background"),
      nb::arg("image"),
      nb::arg("alpha"),
      nb::arg("neighbor_weights"),
      nb::arg("inverse_weight_sum"),
      nb::arg("inverse_weight_sum_plus_one"),
      nb::arg("foreground_gain"),
      nb::arg("background_gain"),
      nb::arg("previous_foreground"),
      nb::arg("previous_background"),
      nb::arg("x_previous_index_map"),
      nb::arg("y_previous_index_map"),
      nb::arg("h"),
      nb::arg("w"));
  m.def(
      "_update_red_black_half_step_from_previous_level_with_boundary_fallback",
      &update_red_black_half_step_from_previous_level_with_boundary_fallback,
      nb::arg("foreground"),
      nb::arg("background"),
      nb::arg("image"),
      nb::arg("alpha"),
      nb::arg("neighbor_weights"),
      nb::arg("inverse_weight_sum"),
      nb::arg("inverse_weight_sum_plus_one"),
      nb::arg("foreground_gain"),
      nb::arg("background_gain"),
      nb::arg("previous_foreground"),
      nb::arg("previous_background"),
      nb::arg("x_previous_index_map"),
      nb::arg("y_previous_index_map"),
      nb::arg("h"),
      nb::arg("w"));
}
