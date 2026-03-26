#include <nanobind/nanobind.h>
#include <nanobind/ndarray.h>

#include <array>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <memory>
#include <limits>
#include <stdexcept>
#include <vector>

namespace nb = nanobind;

namespace {

using Image = nb::ndarray<const float, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using MutableImage = nb::ndarray<float, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using Alpha = nb::ndarray<const float, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using MutableAlpha = nb::ndarray<float, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using Coeff4 = nb::ndarray<float, nb::numpy, nb::shape<-1, -1, 4>, nb::c_contig>;
using IndexMap = nb::ndarray<const std::int32_t, nb::numpy, nb::shape<-1>, nb::c_contig>;
using ImageU8 = nb::ndarray<const std::uint8_t, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using MutableImageU8 = nb::ndarray<std::uint8_t, nb::numpy, nb::shape<-1, -1, 3>, nb::c_contig>;
using AlphaU8 = nb::ndarray<const std::uint8_t, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;
using MutableAlphaU8 = nb::ndarray<std::uint8_t, nb::numpy, nb::shape<-1, -1>, nb::c_contig>;

inline float clamp01(float value) {
    return std::max(0.0f, std::min(1.0f, value));
}

inline std::uint8_t quantize01_to_u8(float value) {
    const int quantized = std::clamp(static_cast<int>(value * 255.0f + 0.5f), 0, 255);
    return static_cast<std::uint8_t>(quantized);
}

inline std::uint32_t div255_fast(std::uint32_t x) {
    return (x + ((x + 257u) >> 8)) >> 8;
}

inline void build_resize_index_map_raw(int src_size, int dst_size, int *index_map) {
    for (int i_dst = 0; i_dst < dst_size; ++i_dst) {
        index_map[i_dst] = std::min(src_size - 1, i_dst * src_size / dst_size);
    }
}

inline void write_solution(
    MutableImage F,
    MutableImage B,
    std::size_t y,
    std::size_t x,
    float a0,
    float image0,
    float image1,
    float image2,
    float sum_wF0,
    float sum_wF1,
    float sum_wF2,
    float sum_wB0,
    float sum_wB1,
    float sum_wB2,
    float inv_W,
    float inv_Wp1,
    float fg_gain,
    float bg_gain
) {
    float a1 = 1.0f - a0;
    float mu_F0 = sum_wF0 * inv_W;
    float mu_F1 = sum_wF1 * inv_W;
    float mu_F2 = sum_wF2 * inv_W;
    float mu_B0 = sum_wB0 * inv_W;
    float mu_B1 = sum_wB1 * inv_W;
    float mu_B2 = sum_wB2 * inv_W;

    float r0 = image0 - a0 * mu_F0 - a1 * mu_B0;
    float r1 = image1 - a0 * mu_F1 - a1 * mu_B1;
    float r2 = image2 - a0 * mu_F2 - a1 * mu_B2;

    if (a0 < 0.01f) {
        F(y, x, 0) = clamp01(mu_F0);
        F(y, x, 1) = clamp01(mu_F1);
        F(y, x, 2) = clamp01(mu_F2);
        B(y, x, 0) = clamp01(mu_B0 + r0 * inv_Wp1);
        B(y, x, 1) = clamp01(mu_B1 + r1 * inv_Wp1);
        B(y, x, 2) = clamp01(mu_B2 + r2 * inv_Wp1);
    } else if (a0 > 0.99f) {
        F(y, x, 0) = clamp01(mu_F0 + r0 * inv_Wp1);
        F(y, x, 1) = clamp01(mu_F1 + r1 * inv_Wp1);
        F(y, x, 2) = clamp01(mu_F2 + r2 * inv_Wp1);
        B(y, x, 0) = clamp01(mu_B0);
        B(y, x, 1) = clamp01(mu_B1);
        B(y, x, 2) = clamp01(mu_B2);
    } else {
        F(y, x, 0) = clamp01(mu_F0 + fg_gain * r0);
        F(y, x, 1) = clamp01(mu_F1 + fg_gain * r1);
        F(y, x, 2) = clamp01(mu_F2 + fg_gain * r2);
        B(y, x, 0) = clamp01(mu_B0 + bg_gain * r0);
        B(y, x, 1) = clamp01(mu_B1 + bg_gain * r1);
        B(y, x, 2) = clamp01(mu_B2 + bg_gain * r2);
    }
}

inline std::size_t scalar_index(std::size_t y, std::size_t x, std::size_t w) {
    return y * w + x;
}

inline std::size_t rgb_index(std::size_t y, std::size_t x, std::size_t w) {
    return (y * w + x) * 3;
}

inline void write_solution_raw(
    float *F,
    float *B,
    std::size_t idx,
    float a0,
    float image0,
    float image1,
    float image2,
    float sum_wF0,
    float sum_wF1,
    float sum_wF2,
    float sum_wB0,
    float sum_wB1,
    float sum_wB2,
    float inv_W,
    float inv_Wp1,
    float fg_gain,
    float bg_gain
) {
    float a1 = 1.0f - a0;
    float mu_F0 = sum_wF0 * inv_W;
    float mu_F1 = sum_wF1 * inv_W;
    float mu_F2 = sum_wF2 * inv_W;
    float mu_B0 = sum_wB0 * inv_W;
    float mu_B1 = sum_wB1 * inv_W;
    float mu_B2 = sum_wB2 * inv_W;

    float r0 = image0 - a0 * mu_F0 - a1 * mu_B0;
    float r1 = image1 - a0 * mu_F1 - a1 * mu_B1;
    float r2 = image2 - a0 * mu_F2 - a1 * mu_B2;

    float *F_px = F + idx * 3;
    float *B_px = B + idx * 3;

    if (a0 < 0.01f) {
        F_px[0] = clamp01(mu_F0);
        F_px[1] = clamp01(mu_F1);
        F_px[2] = clamp01(mu_F2);
        B_px[0] = clamp01(mu_B0 + r0 * inv_Wp1);
        B_px[1] = clamp01(mu_B1 + r1 * inv_Wp1);
        B_px[2] = clamp01(mu_B2 + r2 * inv_Wp1);
    } else if (a0 > 0.99f) {
        F_px[0] = clamp01(mu_F0 + r0 * inv_Wp1);
        F_px[1] = clamp01(mu_F1 + r1 * inv_Wp1);
        F_px[2] = clamp01(mu_F2 + r2 * inv_Wp1);
        B_px[0] = clamp01(mu_B0);
        B_px[1] = clamp01(mu_B1);
        B_px[2] = clamp01(mu_B2);
    } else {
        F_px[0] = clamp01(mu_F0 + fg_gain * r0);
        F_px[1] = clamp01(mu_F1 + fg_gain * r1);
        F_px[2] = clamp01(mu_F2 + fg_gain * r2);
        B_px[0] = clamp01(mu_B0 + bg_gain * r0);
        B_px[1] = clamp01(mu_B1 + bg_gain * r1);
        B_px[2] = clamp01(mu_B2 + bg_gain * r2);
    }
}

inline void compute_initial_means_raw(
    const float *image,
    const float *alpha,
    int h,
    int w,
    float *fg_mean,
    float *bg_mean
) {
    double fg_sum[3] { 0.0, 0.0, 0.0 };
    double bg_sum[3] { 0.0, 0.0, 0.0 };
    int fg_count = 0;
    int bg_count = 0;

    for (int y = 0; y < h; ++y) {
        for (int x = 0; x < w; ++x) {
            std::size_t idx = scalar_index((std::size_t) y, (std::size_t) x, (std::size_t) w);
            const float a0 = alpha[idx];
            const float *px = image + idx * 3;
            if (a0 > 0.9f) {
                fg_sum[0] += px[0];
                fg_sum[1] += px[1];
                fg_sum[2] += px[2];
                ++fg_count;
            }
            if (a0 < 0.1f) {
                bg_sum[0] += px[0];
                bg_sum[1] += px[1];
                bg_sum[2] += px[2];
                ++bg_count;
            }
        }
    }

    if (fg_count > 0) {
        fg_mean[0] = static_cast<float>(fg_sum[0] / fg_count);
        fg_mean[1] = static_cast<float>(fg_sum[1] / fg_count);
        fg_mean[2] = static_cast<float>(fg_sum[2] / fg_count);
    } else {
        fg_mean[0] = 0.0f;
        fg_mean[1] = 0.0f;
        fg_mean[2] = 0.0f;
    }

    if (bg_count > 0) {
        bg_mean[0] = static_cast<float>(bg_sum[0] / bg_count);
        bg_mean[1] = static_cast<float>(bg_sum[1] / bg_count);
        bg_mean[2] = static_cast<float>(bg_sum[2] / bg_count);
    } else {
        bg_mean[0] = 0.0f;
        bg_mean[1] = 0.0f;
        bg_mean[2] = 0.0f;
    }
}

inline void resize_nearest_multichannel_raw(
    float *dst,
    const float *src,
    int h_src,
    int w_src,
    int h_dst,
    int w_dst
) {
    for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
        const int y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
        const float *src_row = src + static_cast<std::size_t>(y_src) * w_src * 3;
        float *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst * 3;
        for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
            const int x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
            const float *src_px = src_row + static_cast<std::size_t>(x_src) * 3;
            float *dst_px = dst_row + static_cast<std::size_t>(x_dst) * 3;
            dst_px[0] = src_px[0];
            dst_px[1] = src_px[1];
            dst_px[2] = src_px[2];
        }
    }
}

inline void resize_nearest_raw(float *dst, const float *src, int h_src, int w_src, int h_dst, int w_dst) {
    for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
        const int y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
        const float *src_row = src + static_cast<std::size_t>(y_src) * w_src;
        float *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst;
        for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
            const int x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
            dst_row[x_dst] = src_row[x_src];
        }
    }
}

inline void resize_nearest_multichannel_u8_raw(
    std::uint8_t *dst,
    const std::uint8_t *src,
    const int *x_map,
    const int *y_map,
    int w_src,
    int h_dst,
    int w_dst
) {
    for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
        const std::uint8_t *src_row = src + static_cast<std::size_t>(y_map[y_dst]) * w_src * 3;
        std::uint8_t *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst * 3;
        for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
            const std::uint8_t *src_px = src_row + static_cast<std::size_t>(x_map[x_dst]) * 3;
            std::uint8_t *dst_px = dst_row + static_cast<std::size_t>(x_dst) * 3;
            dst_px[0] = src_px[0];
            dst_px[1] = src_px[1];
            dst_px[2] = src_px[2];
        }
    }
}

inline void resize_nearest_u8_raw(
    std::uint8_t *dst,
    const std::uint8_t *src,
    const int *x_map,
    const int *y_map,
    int w_src,
    int h_dst,
    int w_dst
) {
    for (int y_dst = 0; y_dst < h_dst; ++y_dst) {
        const std::uint8_t *src_row = src + static_cast<std::size_t>(y_map[y_dst]) * w_src;
        std::uint8_t *dst_row = dst + static_cast<std::size_t>(y_dst) * w_dst;
        for (int x_dst = 0; x_dst < w_dst; ++x_dst) {
            dst_row[x_dst] = src_row[x_map[x_dst]];
        }
    }
}

inline void compute_initial_means_u8_raw(
    const std::uint8_t *image,
    const std::uint8_t *alpha,
    int h,
    int w,
    std::uint8_t fg_mean[3],
    std::uint8_t bg_mean[3]
) {
    double fg_sum[3] { 0.0, 0.0, 0.0 };
    double bg_sum[3] { 0.0, 0.0, 0.0 };
    int fg_count = 0;
    int bg_count = 0;

    for (int y = 0; y < h; ++y) {
        for (int x = 0; x < w; ++x) {
            const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
            const std::uint8_t a0 = alpha[idx];
            const std::uint8_t *px = image + idx * 3;
            if (a0 >= 230) {
                fg_sum[0] += px[0];
                fg_sum[1] += px[1];
                fg_sum[2] += px[2];
                ++fg_count;
            }
            if (a0 <= 25) {
                bg_sum[0] += px[0];
                bg_sum[1] += px[1];
                bg_sum[2] += px[2];
                ++bg_count;
            }
        }
    }

    for (int c = 0; c < 3; ++c) {
        fg_mean[c] = fg_count > 0 ? static_cast<std::uint8_t>(std::clamp<int>(
                                     static_cast<int>(std::lround(fg_sum[c] / fg_count)),
                                     0,
                                     255))
                                 : static_cast<std::uint8_t>(0);
        bg_mean[c] = bg_count > 0 ? static_cast<std::uint8_t>(std::clamp<int>(
                                     static_cast<int>(std::lround(bg_sum[c] / bg_count)),
                                     0,
                                     255))
                                 : static_cast<std::uint8_t>(0);
    }
}

inline void build_level_coefficients_u8_raw(
    const std::uint8_t *alpha,
    int h,
    int w,
    const std::uint32_t *weight_lut,
    float weight_scale_inv,
    const float *u8_to_f32,
    float *neighbor_weights,
    float *inv_W,
    float *inv_Wp1,
    float *fg_gain,
    float *bg_gain
) {
    if (h <= 0 || w <= 0) {
        return;
    }

    auto lookup_weight = [&](std::uint8_t a0, std::uint8_t a1) {
        return static_cast<float>(weight_lut[static_cast<std::size_t>(a0) * 256 + a1]) * weight_scale_inv;
    };

    auto process_interior_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
        const std::uint8_t a0 = alpha[idx];
        const float a0_f = u8_to_f32[a0];
        const float a1_f = 1.0f - a0_f;

        const float w0 = lookup_weight(a0, alpha[idx - 1]);
        const float w1 = lookup_weight(a0, alpha[idx + 1]);
        const float w2 = lookup_weight(a0, alpha[idx - static_cast<std::size_t>(w)]);
        const float w3 = lookup_weight(a0, alpha[idx + static_cast<std::size_t>(w)]);

        float *nw = neighbor_weights + idx * 4;
        nw[0] = w0;
        nw[1] = w1;
        nw[2] = w2;
        nw[3] = w3;

        const float W = w0 + w1 + w2 + w3;
        inv_W[idx] = 1.0f / W;
        inv_Wp1[idx] = 1.0f / (W + 1.0f);

        const float D = W + a0_f * a0_f + a1_f * a1_f;
        const float inv_D = 1.0f / D;
        fg_gain[idx] = a0_f * inv_D;
        bg_gain[idx] = a1_f * inv_D;
    };

    auto process_boundary_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
        const std::uint8_t a0 = alpha[idx];
        const float a0_f = u8_to_f32[a0];
        const float a1_f = 1.0f - a0_f;

        const int x_left = x == 0 ? 0 : x - 1;
        const int x_right = std::min(w - 1, x + 1);
        const int y_up = y == 0 ? 0 : y - 1;
        const int y_down = std::min(h - 1, y + 1);

        const float w0 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w))]);
        const float w1 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w))]);
        const float w2 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);
        const float w3 = lookup_weight(a0, alpha[scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w))]);

        float *nw = neighbor_weights + idx * 4;
        nw[0] = w0;
        nw[1] = w1;
        nw[2] = w2;
        nw[3] = w3;

        const float W = w0 + w1 + w2 + w3;
        inv_W[idx] = 1.0f / W;
        inv_Wp1[idx] = 1.0f / (W + 1.0f);

        const float D = W + a0_f * a0_f + a1_f * a1_f;
        const float inv_D = 1.0f / D;
        fg_gain[idx] = a0_f * inv_D;
        bg_gain[idx] = a1_f * inv_D;
    };

    if (h > 2 && w > 2) {
        for (int y = 1; y < h - 1; ++y) {
            for (int x = 1; x < w - 1; ++x) {
                process_interior_pixel(y, x);
            }
        }
    }

    for (int x = 0; x < w; ++x) {
        process_boundary_pixel(0, x);
    }

    if (h > 1) {
        for (int x = 0; x < w; ++x) {
            process_boundary_pixel(h - 1, x);
        }
    }

    for (int y = 1; y < h - 1; ++y) {
        process_boundary_pixel(y, 0);
        if (w > 1) {
            process_boundary_pixel(y, w - 1);
        }
    }
}

inline void build_level_coefficients_raw(
    const float *alpha,
    int h,
    int w,
    float eps,
    float omega,
    float *neighbor_weights,
    float *inv_W,
    float *inv_Wp1,
    float *fg_gain,
    float *bg_gain
) {
    if (h <= 0 || w <= 0) {
        return;
    }

    auto process_interior_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index((std::size_t) y, (std::size_t) x, (std::size_t) w);
        const float a0 = alpha[idx];
        const float a1 = 1.0f - a0;

        const float w0 = eps + omega * std::fabs(a0 - alpha[idx - 1]);
        const float w1 = eps + omega * std::fabs(a0 - alpha[idx + 1]);
        const float w2 = eps + omega * std::fabs(a0 - alpha[idx - static_cast<std::size_t>(w)]);
        const float w3 = eps + omega * std::fabs(a0 - alpha[idx + static_cast<std::size_t>(w)]);

        float *nw = neighbor_weights + idx * 4;
        nw[0] = w0;
        nw[1] = w1;
        nw[2] = w2;
        nw[3] = w3;

        const float W = w0 + w1 + w2 + w3;
        inv_W[idx] = 1.0f / W;
        inv_Wp1[idx] = 1.0f / (W + 1.0f);

        const float D = W + a0 * a0 + a1 * a1;
        const float inv_D = 1.0f / D;
        fg_gain[idx] = a0 * inv_D;
        bg_gain[idx] = a1 * inv_D;
    };

    auto process_boundary_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index((std::size_t) y, (std::size_t) x, (std::size_t) w);
        const float a0 = alpha[idx];
        const float a1 = 1.0f - a0;

        const int x_left = x == 0 ? 0 : x - 1;
        const int x_right = std::min(w - 1, x + 1);
        const int y_up = y == 0 ? 0 : y - 1;
        const int y_down = std::min(h - 1, y + 1);

        const float w0 =
            eps + omega * std::fabs(a0 - alpha[scalar_index((std::size_t) y, (std::size_t) x_left, (std::size_t) w)]);
        const float w1 = eps +
            omega * std::fabs(a0 - alpha[scalar_index((std::size_t) y, (std::size_t) x_right, (std::size_t) w)]);
        const float w2 =
            eps + omega * std::fabs(a0 - alpha[scalar_index((std::size_t) y_up, (std::size_t) x, (std::size_t) w)]);
        const float w3 = eps +
            omega * std::fabs(a0 - alpha[scalar_index((std::size_t) y_down, (std::size_t) x, (std::size_t) w)]);

        float *nw = neighbor_weights + idx * 4;
        nw[0] = w0;
        nw[1] = w1;
        nw[2] = w2;
        nw[3] = w3;

        const float W = w0 + w1 + w2 + w3;
        inv_W[idx] = 1.0f / W;
        inv_Wp1[idx] = 1.0f / (W + 1.0f);

        const float D = W + a0 * a0 + a1 * a1;
        const float inv_D = 1.0f / D;
        fg_gain[idx] = a0 * inv_D;
        bg_gain[idx] = a1 * inv_D;
    };

    if (h > 2 && w > 2) {
        for (int y = 1; y < h - 1; ++y) {
            for (int x = 1; x < w - 1; ++x) {
                process_interior_pixel(y, x);
            }
        }
    }

    for (int x = 0; x < w; ++x) {
        process_boundary_pixel(0, x);
    }

    if (h > 1) {
        for (int x = 0; x < w; ++x) {
            process_boundary_pixel(h - 1, x);
        }
    }

    for (int y = 1; y < h - 1; ++y) {
        process_boundary_pixel(y, 0);
        if (w > 1) {
            process_boundary_pixel(y, w - 1);
        }
    }
}

inline void update_rb_half_cached_raw(
    float *F,
    float *B,
    const float *image,
    const float *alpha,
    const float *neighbor_weights,
    const float *inv_W,
    const float *inv_Wp1,
    const float *fg_gain,
    const float *bg_gain,
    int h,
    int w,
    int color
) {
    if (h <= 0 || w <= 0) {
        return;
    }

    auto process_interior_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index((std::size_t) y, (std::size_t) x, (std::size_t) w);
        const float a0 = alpha[idx];
        const float *nw = neighbor_weights + idx * 4;

        const std::size_t idx_left = idx - 1;
        const std::size_t idx_right = idx + 1;
        const std::size_t idx_up = idx - static_cast<std::size_t>(w);
        const std::size_t idx_down = idx + static_cast<std::size_t>(w);

        const float *F_left = F + idx_left * 3;
        const float *F_right = F + idx_right * 3;
        const float *F_up = F + idx_up * 3;
        const float *F_down = F + idx_down * 3;
        const float *B_left = B + idx_left * 3;
        const float *B_right = B + idx_right * 3;
        const float *B_up = B + idx_up * 3;
        const float *B_down = B + idx_down * 3;

        const float sum_wF0 = nw[0] * F_left[0] + nw[1] * F_right[0] + nw[2] * F_up[0] + nw[3] * F_down[0];
        const float sum_wF1 = nw[0] * F_left[1] + nw[1] * F_right[1] + nw[2] * F_up[1] + nw[3] * F_down[1];
        const float sum_wF2 = nw[0] * F_left[2] + nw[1] * F_right[2] + nw[2] * F_up[2] + nw[3] * F_down[2];
        const float sum_wB0 = nw[0] * B_left[0] + nw[1] * B_right[0] + nw[2] * B_up[0] + nw[3] * B_down[0];
        const float sum_wB1 = nw[0] * B_left[1] + nw[1] * B_right[1] + nw[2] * B_up[1] + nw[3] * B_down[1];
        const float sum_wB2 = nw[0] * B_left[2] + nw[1] * B_right[2] + nw[2] * B_up[2] + nw[3] * B_down[2];

        const std::size_t image_idx = idx * 3;
        write_solution_raw(
            F,
            B,
            idx,
            a0,
            image[image_idx],
            image[image_idx + 1],
            image[image_idx + 2],
            sum_wF0,
            sum_wF1,
            sum_wF2,
            sum_wB0,
            sum_wB1,
            sum_wB2,
            inv_W[idx],
            inv_Wp1[idx],
            fg_gain[idx],
            bg_gain[idx]);
    };

    auto process_boundary_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index((std::size_t) y, (std::size_t) x, (std::size_t) w);
        const float a0 = alpha[idx];
        const float *nw = neighbor_weights + idx * 4;

        float sum_wF0 = 0.0f;
        float sum_wF1 = 0.0f;
        float sum_wF2 = 0.0f;
        float sum_wB0 = 0.0f;
        float sum_wB1 = 0.0f;
        float sum_wB2 = 0.0f;

        const int x_left = x == 0 ? 0 : x - 1;
        const int x_right = x + 1 >= w ? w - 1 : x + 1;
        const int y_up = y == 0 ? 0 : y - 1;
        const int y_down = y + 1 >= h ? h - 1 : y + 1;

        const std::size_t idx_left = scalar_index((std::size_t) y, (std::size_t) x_left, (std::size_t) w);
        const std::size_t idx_right = scalar_index((std::size_t) y, (std::size_t) x_right, (std::size_t) w);
        const std::size_t idx_up = scalar_index((std::size_t) y_up, (std::size_t) x, (std::size_t) w);
        const std::size_t idx_down = scalar_index((std::size_t) y_down, (std::size_t) x, (std::size_t) w);

        const float *F_left = F + idx_left * 3;
        const float *F_right = F + idx_right * 3;
        const float *F_up = F + idx_up * 3;
        const float *F_down = F + idx_down * 3;
        const float *B_left = B + idx_left * 3;
        const float *B_right = B + idx_right * 3;
        const float *B_up = B + idx_up * 3;
        const float *B_down = B + idx_down * 3;

        sum_wF0 = nw[0] * F_left[0] + nw[1] * F_right[0] + nw[2] * F_up[0] + nw[3] * F_down[0];
        sum_wF1 = nw[0] * F_left[1] + nw[1] * F_right[1] + nw[2] * F_up[1] + nw[3] * F_down[1];
        sum_wF2 = nw[0] * F_left[2] + nw[1] * F_right[2] + nw[2] * F_up[2] + nw[3] * F_down[2];
        sum_wB0 = nw[0] * B_left[0] + nw[1] * B_right[0] + nw[2] * B_up[0] + nw[3] * B_down[0];
        sum_wB1 = nw[0] * B_left[1] + nw[1] * B_right[1] + nw[2] * B_up[1] + nw[3] * B_down[1];
        sum_wB2 = nw[0] * B_left[2] + nw[1] * B_right[2] + nw[2] * B_up[2] + nw[3] * B_down[2];

        const std::size_t image_idx = idx * 3;
        write_solution_raw(
            F,
            B,
            idx,
            a0,
            image[image_idx],
            image[image_idx + 1],
            image[image_idx + 2],
            sum_wF0,
            sum_wF1,
            sum_wF2,
            sum_wB0,
            sum_wB1,
            sum_wB2,
            inv_W[idx],
            inv_Wp1[idx],
            fg_gain[idx],
            bg_gain[idx]);
    };

    if (h > 2 && w > 2) {
        for (int y = 1; y < h - 1; ++y) {
            int x_start = (color + y) % 2;
            x_start = x_start == 0 ? 2 : 1;
            for (int x = x_start; x < w - 1; x += 2) {
                process_interior_pixel(y, x);
            }
        }
    }

    for (int y = 0; y < h; ++y) {
        const bool boundary_row = y == 0 || y + 1 >= h;
        if (!boundary_row) {
            continue;
        }

        const int x_start = (color + y) % 2;
        for (int x = x_start; x < w; x += 2) {
            process_boundary_pixel(y, x);
        }
    }

    for (int y = 1; y < h - 1; ++y) {
        if (((color + y) % 2) == 0) {
            process_boundary_pixel(y, 0);
        }
        if (w > 1 && ((w - 1 + y) % 2) == color) {
            process_boundary_pixel(y, w - 1);
        }
    }
}

inline void write_solution_u8(
    std::uint8_t *F,
    std::uint8_t *B,
    std::size_t idx,
    float a0,
    float image0,
    float image1,
    float image2,
    float sum_wF0,
    float sum_wF1,
    float sum_wF2,
    float sum_wB0,
    float sum_wB1,
    float sum_wB2,
    float inv_W,
    float inv_Wp1,
    float fg_gain,
    float bg_gain
) {
    float a1 = 1.0f - a0;
    float mu_F0 = sum_wF0 * inv_W;
    float mu_F1 = sum_wF1 * inv_W;
    float mu_F2 = sum_wF2 * inv_W;
    float mu_B0 = sum_wB0 * inv_W;
    float mu_B1 = sum_wB1 * inv_W;
    float mu_B2 = sum_wB2 * inv_W;

    float r0 = image0 - a0 * mu_F0 - a1 * mu_B0;
    float r1 = image1 - a0 * mu_F1 - a1 * mu_B1;
    float r2 = image2 - a0 * mu_F2 - a1 * mu_B2;

    std::uint8_t *F_px = F + idx * 3;
    std::uint8_t *B_px = B + idx * 3;

    if (a0 < 0.01f) {
        F_px[0] = quantize01_to_u8(mu_F0);
        F_px[1] = quantize01_to_u8(mu_F1);
        F_px[2] = quantize01_to_u8(mu_F2);
        B_px[0] = quantize01_to_u8(mu_B0 + r0 * inv_Wp1);
        B_px[1] = quantize01_to_u8(mu_B1 + r1 * inv_Wp1);
        B_px[2] = quantize01_to_u8(mu_B2 + r2 * inv_Wp1);
    } else if (a0 > 0.99f) {
        F_px[0] = quantize01_to_u8(mu_F0 + r0 * inv_Wp1);
        F_px[1] = quantize01_to_u8(mu_F1 + r1 * inv_Wp1);
        F_px[2] = quantize01_to_u8(mu_F2 + r2 * inv_Wp1);
        B_px[0] = quantize01_to_u8(mu_B0);
        B_px[1] = quantize01_to_u8(mu_B1);
        B_px[2] = quantize01_to_u8(mu_B2);
    } else {
        F_px[0] = quantize01_to_u8(mu_F0 + fg_gain * r0);
        F_px[1] = quantize01_to_u8(mu_F1 + fg_gain * r1);
        F_px[2] = quantize01_to_u8(mu_F2 + fg_gain * r2);
        B_px[0] = quantize01_to_u8(mu_B0 + bg_gain * r0);
        B_px[1] = quantize01_to_u8(mu_B1 + bg_gain * r1);
        B_px[2] = quantize01_to_u8(mu_B2 + bg_gain * r2);
    }
}

inline void update_rb_half_cached_u8_raw(
    std::uint8_t *F,
    std::uint8_t *B,
    const std::uint8_t *image,
    const std::uint8_t *alpha,
    const float *u8_to_f32,
    const float *neighbor_weights,
    const float *inv_W,
    const float *inv_Wp1,
    const float *fg_gain,
    const float *bg_gain,
    int h,
    int w,
    int color
) {
    if (h <= 0 || w <= 0) {
        return;
    }

    auto process_interior_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
        const float a0 = u8_to_f32[alpha[idx]];

        const std::size_t idx_left = idx - 1;
        const std::size_t idx_right = idx + 1;
        const std::size_t idx_up = idx - static_cast<std::size_t>(w);
        const std::size_t idx_down = idx + static_cast<std::size_t>(w);

        const float w0 = neighbor_weights[idx * 4 + 0];
        const float w1 = neighbor_weights[idx * 4 + 1];
        const float w2 = neighbor_weights[idx * 4 + 2];
        const float w3 = neighbor_weights[idx * 4 + 3];

        const float F_left0 = u8_to_f32[F[idx_left * 3 + 0]];
        const float F_left1 = u8_to_f32[F[idx_left * 3 + 1]];
        const float F_left2 = u8_to_f32[F[idx_left * 3 + 2]];
        const float F_right0 = u8_to_f32[F[idx_right * 3 + 0]];
        const float F_right1 = u8_to_f32[F[idx_right * 3 + 1]];
        const float F_right2 = u8_to_f32[F[idx_right * 3 + 2]];
        const float F_up0 = u8_to_f32[F[idx_up * 3 + 0]];
        const float F_up1 = u8_to_f32[F[idx_up * 3 + 1]];
        const float F_up2 = u8_to_f32[F[idx_up * 3 + 2]];
        const float F_down0 = u8_to_f32[F[idx_down * 3 + 0]];
        const float F_down1 = u8_to_f32[F[idx_down * 3 + 1]];
        const float F_down2 = u8_to_f32[F[idx_down * 3 + 2]];

        const float B_left0 = u8_to_f32[B[idx_left * 3 + 0]];
        const float B_left1 = u8_to_f32[B[idx_left * 3 + 1]];
        const float B_left2 = u8_to_f32[B[idx_left * 3 + 2]];
        const float B_right0 = u8_to_f32[B[idx_right * 3 + 0]];
        const float B_right1 = u8_to_f32[B[idx_right * 3 + 1]];
        const float B_right2 = u8_to_f32[B[idx_right * 3 + 2]];
        const float B_up0 = u8_to_f32[B[idx_up * 3 + 0]];
        const float B_up1 = u8_to_f32[B[idx_up * 3 + 1]];
        const float B_up2 = u8_to_f32[B[idx_up * 3 + 2]];
        const float B_down0 = u8_to_f32[B[idx_down * 3 + 0]];
        const float B_down1 = u8_to_f32[B[idx_down * 3 + 1]];
        const float B_down2 = u8_to_f32[B[idx_down * 3 + 2]];

        const float sum_wF0 = w0 * F_left0 + w1 * F_right0 + w2 * F_up0 + w3 * F_down0;
        const float sum_wF1 = w0 * F_left1 + w1 * F_right1 + w2 * F_up1 + w3 * F_down1;
        const float sum_wF2 = w0 * F_left2 + w1 * F_right2 + w2 * F_up2 + w3 * F_down2;
        const float sum_wB0 = w0 * B_left0 + w1 * B_right0 + w2 * B_up0 + w3 * B_down0;
        const float sum_wB1 = w0 * B_left1 + w1 * B_right1 + w2 * B_up1 + w3 * B_down1;
        const float sum_wB2 = w0 * B_left2 + w1 * B_right2 + w2 * B_up2 + w3 * B_down2;

        const std::size_t image_idx = idx * 3;
        write_solution_u8(
            F,
            B,
            idx,
            a0,
            u8_to_f32[image[image_idx + 0]],
            u8_to_f32[image[image_idx + 1]],
            u8_to_f32[image[image_idx + 2]],
            sum_wF0,
            sum_wF1,
            sum_wF2,
            sum_wB0,
            sum_wB1,
            sum_wB2,
            inv_W[idx],
            inv_Wp1[idx],
            fg_gain[idx],
            bg_gain[idx]);
    };

    auto process_boundary_pixel = [&](int y, int x) {
        const std::size_t idx = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
        const float a0 = u8_to_f32[alpha[idx]];

        const int x_left = x == 0 ? 0 : x - 1;
        const int x_right = x + 1 >= w ? w - 1 : x + 1;
        const int y_up = y == 0 ? 0 : y - 1;
        const int y_down = y + 1 >= h ? h - 1 : y + 1;

        const std::size_t idx_left = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_left), static_cast<std::size_t>(w));
        const std::size_t idx_right = scalar_index(static_cast<std::size_t>(y), static_cast<std::size_t>(x_right), static_cast<std::size_t>(w));
        const std::size_t idx_up = scalar_index(static_cast<std::size_t>(y_up), static_cast<std::size_t>(x), static_cast<std::size_t>(w));
        const std::size_t idx_down = scalar_index(static_cast<std::size_t>(y_down), static_cast<std::size_t>(x), static_cast<std::size_t>(w));

        const float w0 = neighbor_weights[idx * 4 + 0];
        const float w1 = neighbor_weights[idx * 4 + 1];
        const float w2 = neighbor_weights[idx * 4 + 2];
        const float w3 = neighbor_weights[idx * 4 + 3];

        const float F_left0 = u8_to_f32[F[idx_left * 3 + 0]];
        const float F_left1 = u8_to_f32[F[idx_left * 3 + 1]];
        const float F_left2 = u8_to_f32[F[idx_left * 3 + 2]];
        const float F_right0 = u8_to_f32[F[idx_right * 3 + 0]];
        const float F_right1 = u8_to_f32[F[idx_right * 3 + 1]];
        const float F_right2 = u8_to_f32[F[idx_right * 3 + 2]];
        const float F_up0 = u8_to_f32[F[idx_up * 3 + 0]];
        const float F_up1 = u8_to_f32[F[idx_up * 3 + 1]];
        const float F_up2 = u8_to_f32[F[idx_up * 3 + 2]];
        const float F_down0 = u8_to_f32[F[idx_down * 3 + 0]];
        const float F_down1 = u8_to_f32[F[idx_down * 3 + 1]];
        const float F_down2 = u8_to_f32[F[idx_down * 3 + 2]];

        const float B_left0 = u8_to_f32[B[idx_left * 3 + 0]];
        const float B_left1 = u8_to_f32[B[idx_left * 3 + 1]];
        const float B_left2 = u8_to_f32[B[idx_left * 3 + 2]];
        const float B_right0 = u8_to_f32[B[idx_right * 3 + 0]];
        const float B_right1 = u8_to_f32[B[idx_right * 3 + 1]];
        const float B_right2 = u8_to_f32[B[idx_right * 3 + 2]];
        const float B_up0 = u8_to_f32[B[idx_up * 3 + 0]];
        const float B_up1 = u8_to_f32[B[idx_up * 3 + 1]];
        const float B_up2 = u8_to_f32[B[idx_up * 3 + 2]];
        const float B_down0 = u8_to_f32[B[idx_down * 3 + 0]];
        const float B_down1 = u8_to_f32[B[idx_down * 3 + 1]];
        const float B_down2 = u8_to_f32[B[idx_down * 3 + 2]];

        const float sum_wF0 = w0 * F_left0 + w1 * F_right0 + w2 * F_up0 + w3 * F_down0;
        const float sum_wF1 = w0 * F_left1 + w1 * F_right1 + w2 * F_up1 + w3 * F_down1;
        const float sum_wF2 = w0 * F_left2 + w1 * F_right2 + w2 * F_up2 + w3 * F_down2;
        const float sum_wB0 = w0 * B_left0 + w1 * B_right0 + w2 * B_up0 + w3 * B_down0;
        const float sum_wB1 = w0 * B_left1 + w1 * B_right1 + w2 * B_up1 + w3 * B_down1;
        const float sum_wB2 = w0 * B_left2 + w1 * B_right2 + w2 * B_up2 + w3 * B_down2;

        const std::size_t image_idx = idx * 3;
        write_solution_u8(
            F,
            B,
            idx,
            a0,
            u8_to_f32[image[image_idx + 0]],
            u8_to_f32[image[image_idx + 1]],
            u8_to_f32[image[image_idx + 2]],
            sum_wF0,
            sum_wF1,
            sum_wF2,
            sum_wB0,
            sum_wB1,
            sum_wB2,
            inv_W[idx],
            inv_Wp1[idx],
            fg_gain[idx],
            bg_gain[idx]);
    };

    if (h > 2 && w > 2) {
        for (int y = 1; y < h - 1; ++y) {
            int x_start = (color + y) % 2;
            x_start = x_start == 0 ? 2 : 1;
            for (int x = x_start; x < w - 1; x += 2) {
                process_interior_pixel(y, x);
            }
        }
    }

    for (int y = 0; y < h; ++y) {
        const bool boundary_row = y == 0 || y + 1 >= h;
        if (!boundary_row) {
            continue;
        }

        const int x_start = (color + y) % 2;
        for (int x = x_start; x < w; x += 2) {
            process_boundary_pixel(y, x);
        }
    }

    for (int y = 1; y < h - 1; ++y) {
        if (((color + y) % 2) == 0) {
            process_boundary_pixel(y, 0);
        }
        if (w > 1 && ((w - 1 + y) % 2) == color) {
            process_boundary_pixel(y, w - 1);
        }
    }
}

void estimate_fb_ml_u8(
    MutableImageU8 F_out,
    MutableImageU8 B_out,
    ImageU8 input_image,
    AlphaU8 input_alpha,
    float regularization,
    float gradient_weight,
    int n_small_iterations,
    int n_big_iterations,
    int small_size
) {
    const int h0 = static_cast<int>(input_image.shape(0));
    const int w0 = static_cast<int>(input_image.shape(1));

    if (static_cast<int>(F_out.shape(0)) != h0 || static_cast<int>(F_out.shape(1)) != w0 ||
        static_cast<int>(F_out.shape(2)) != 3 || static_cast<int>(B_out.shape(0)) != h0 ||
        static_cast<int>(B_out.shape(1)) != w0 || static_cast<int>(B_out.shape(2)) != 3) {
        throw std::runtime_error("estimate_fb_ml_u8: output shapes must match the input image");
    }
    if (h0 <= 0 || w0 <= 0) {
        throw std::runtime_error("estimate_fb_ml_u8: input image must be non-empty");
    }

    const auto *input_image_ptr = input_image.data();
    const auto *input_alpha_ptr = input_alpha.data();

    nb::gil_scoped_release release;

    const std::size_t max_pixels = static_cast<std::size_t>(h0) * static_cast<std::size_t>(w0);
    std::unique_ptr<std::uint8_t[]> prevF_storage(new std::uint8_t[max_pixels * 3]);
    std::unique_ptr<std::uint8_t[]> prevB_storage(new std::uint8_t[max_pixels * 3]);
    std::unique_ptr<std::uint8_t[]> currF_storage(new std::uint8_t[max_pixels * 3]);
    std::unique_ptr<std::uint8_t[]> currB_storage(new std::uint8_t[max_pixels * 3]);
    std::unique_ptr<std::uint8_t[]> image(new std::uint8_t[max_pixels * 3]);
    std::unique_ptr<std::uint8_t[]> alpha(new std::uint8_t[max_pixels]);
    std::unique_ptr<float[]> neighbor_weights(new float[max_pixels * 4]);
    std::unique_ptr<float[]> inv_W(new float[max_pixels]);
    std::unique_ptr<float[]> inv_Wp1(new float[max_pixels]);
    std::unique_ptr<float[]> fg_gain(new float[max_pixels]);
    std::unique_ptr<float[]> bg_gain(new float[max_pixels]);
    std::unique_ptr<std::uint32_t[]> weight_lut(new std::uint32_t[256 * 256]);

    constexpr float weight_scale = 65536.0f;
    constexpr float weight_scale_inv = 1.0f / weight_scale;
    constexpr float inv255 = 1.0f / 255.0f;
    constexpr float inv256 = 1.0f / 256.0f;
    std::array<float, 256> u8_to_f32 {};
    for (int i = 0; i < 256; ++i) {
        u8_to_f32[static_cast<std::size_t>(i)] = static_cast<float>(i) * inv255;
    }

    for (int a0 = 0; a0 < 256; ++a0) {
        for (int a1 = 0; a1 < 256; ++a1) {
            // The alpha difference is 8-bit, so a 256x fixed-point step stays in the
            // exact 0..65535 range supported by the fast div255 helper.
            const std::uint32_t diff_q8 = div255_fast(static_cast<std::uint32_t>(std::abs(a0 - a1)) * 256u);
            const float diff = static_cast<float>(diff_q8) * inv256;
            const double scaled = static_cast<double>(regularization + gradient_weight * diff) * weight_scale;
            const double clamped = std::max(0.0, std::min(scaled, static_cast<double>(std::numeric_limits<std::uint32_t>::max())));
            weight_lut[static_cast<std::size_t>(a0) * 256 + a1] = static_cast<std::uint32_t>(std::lround(clamped));
        }
    }

    std::uint8_t fg_mean[3];
    std::uint8_t bg_mean[3];
    compute_initial_means_u8_raw(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

    prevF_storage[0] = fg_mean[0];
    prevF_storage[1] = fg_mean[1];
    prevF_storage[2] = fg_mean[2];
    prevB_storage[0] = bg_mean[0];
    prevB_storage[1] = bg_mean[1];
    prevB_storage[2] = bg_mean[2];

    int prev_h = 1;
    int prev_w = 1;

    const int max_dim = std::max(h0, w0);
    const int n_levels = (max_dim <= 1) ? 0 : static_cast<int>(std::ceil(std::log2(static_cast<double>(max_dim))));

    std::vector<int> x_map;
    std::vector<int> y_map;
    std::vector<int> prev_x_map;
    std::vector<int> prev_y_map;

    for (int i_level = 0; i_level <= n_levels; ++i_level) {
        int w;
        int h;
        int n_iter;

        if (max_dim <= 1) {
            w = 1;
            h = 1;
            n_iter = n_small_iterations;
        } else {
            const double ratio = static_cast<double>(i_level) / static_cast<double>(n_levels);
            w = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(w0), ratio)));
            h = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(h0), ratio)));
            n_iter = (w <= small_size && h <= small_size) ? n_small_iterations : n_big_iterations;
        }

        x_map.resize(static_cast<std::size_t>(w));
        y_map.resize(static_cast<std::size_t>(h));
        build_resize_index_map_raw(w0, w, x_map.data());
        build_resize_index_map_raw(h0, h, y_map.data());
        resize_nearest_multichannel_u8_raw(image.get(), input_image_ptr, x_map.data(), y_map.data(), w0, h, w);
        resize_nearest_u8_raw(alpha.get(), input_alpha_ptr, x_map.data(), y_map.data(), w0, h, w);
        build_level_coefficients_u8_raw(
            alpha.get(),
            h,
            w,
            weight_lut.get(),
            weight_scale_inv,
            u8_to_f32.data(),
            neighbor_weights.get(),
            inv_W.get(),
            inv_Wp1.get(),
            fg_gain.get(),
            bg_gain.get());

        const bool final_level = i_level == n_levels;
        std::uint8_t *currF = final_level ? F_out.data() : currF_storage.get();
        std::uint8_t *currB = final_level ? B_out.data() : currB_storage.get();

        prev_x_map.resize(static_cast<std::size_t>(w));
        prev_y_map.resize(static_cast<std::size_t>(h));
        build_resize_index_map_raw(prev_w, w, prev_x_map.data());
        build_resize_index_map_raw(prev_h, h, prev_y_map.data());

        resize_nearest_multichannel_u8_raw(currF, prevF_storage.get(), prev_x_map.data(), prev_y_map.data(), prev_w, h, w);
        resize_nearest_multichannel_u8_raw(currB, prevB_storage.get(), prev_x_map.data(), prev_y_map.data(), prev_w, h, w);

        for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
            update_rb_half_cached_u8_raw(
                currF,
                currB,
                image.get(),
                alpha.get(),
                u8_to_f32.data(),
                neighbor_weights.get(),
                inv_W.get(),
                inv_Wp1.get(),
                fg_gain.get(),
                bg_gain.get(),
                h,
                w,
                0);
            update_rb_half_cached_u8_raw(
                currF,
                currB,
                image.get(),
                alpha.get(),
                u8_to_f32.data(),
                neighbor_weights.get(),
                inv_W.get(),
                inv_Wp1.get(),
                fg_gain.get(),
                bg_gain.get(),
                h,
                w,
                1);
        }

        if (!final_level) {
            std::swap(prevF_storage, currF_storage);
            std::swap(prevB_storage, currB_storage);
            prev_h = h;
            prev_w = w;
        }
    }
}

void estimate_fb_ml(
    MutableImage F_out,
    MutableImage B_out,
    Image input_image,
    Alpha input_alpha,
    float regularization,
    float gradient_weight,
    int n_small_iterations,
    int n_big_iterations,
    int small_size
) {
    const int h0 = static_cast<int>(input_image.shape(0));
    const int w0 = static_cast<int>(input_image.shape(1));

    if (static_cast<int>(F_out.shape(0)) != h0 || static_cast<int>(F_out.shape(1)) != w0 ||
        static_cast<int>(F_out.shape(2)) != 3 || static_cast<int>(B_out.shape(0)) != h0 ||
        static_cast<int>(B_out.shape(1)) != w0 || static_cast<int>(B_out.shape(2)) != 3) {
        throw std::runtime_error("estimate_fb_ml: output shapes must match the input image");
    }
    if (h0 <= 0 || w0 <= 0) {
        throw std::runtime_error("estimate_fb_ml: input image must be non-empty");
    }

    const float *input_image_ptr = input_image.data();
    const float *input_alpha_ptr = input_alpha.data();

    nb::gil_scoped_release release;

    const std::size_t max_pixels = static_cast<std::size_t>(h0) * static_cast<std::size_t>(w0);
    std::unique_ptr<float[]> prevF_storage(new float[max_pixels * 3]);
    std::unique_ptr<float[]> prevB_storage(new float[max_pixels * 3]);
    std::unique_ptr<float[]> currF_storage(new float[max_pixels * 3]);
    std::unique_ptr<float[]> currB_storage(new float[max_pixels * 3]);
    std::unique_ptr<float[]> image(new float[max_pixels * 3]);
    std::unique_ptr<float[]> alpha(new float[max_pixels]);
    std::unique_ptr<float[]> neighbor_weights(new float[max_pixels * 4]);
    std::unique_ptr<float[]> inv_W(new float[max_pixels]);
    std::unique_ptr<float[]> inv_Wp1(new float[max_pixels]);
    std::unique_ptr<float[]> fg_gain(new float[max_pixels]);
    std::unique_ptr<float[]> bg_gain(new float[max_pixels]);

    float fg_mean[3];
    float bg_mean[3];
    compute_initial_means_raw(input_image_ptr, input_alpha_ptr, h0, w0, fg_mean, bg_mean);

    prevF_storage[0] = fg_mean[0];
    prevF_storage[1] = fg_mean[1];
    prevF_storage[2] = fg_mean[2];
    prevB_storage[0] = bg_mean[0];
    prevB_storage[1] = bg_mean[1];
    prevB_storage[2] = bg_mean[2];

    int prev_h = 1;
    int prev_w = 1;

    const float eps = regularization;
    const float omega = gradient_weight;
    const int max_dim = std::max(h0, w0);
    const int n_levels = (max_dim <= 1) ? 0 : static_cast<int>(std::ceil(std::log2(static_cast<double>(max_dim))));

    for (int i_level = 0; i_level <= n_levels; ++i_level) {
        int w;
        int h;
        int n_iter;

        if (max_dim <= 1) {
            w = 1;
            h = 1;
            n_iter = n_small_iterations;
        } else {
            const double ratio = static_cast<double>(i_level) / static_cast<double>(n_levels);
            w = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(w0), ratio)));
            h = static_cast<int>(std::nearbyint(std::pow(static_cast<double>(h0), ratio)));
            n_iter = (w <= small_size && h <= small_size) ? n_small_iterations : n_big_iterations;
        }

        resize_nearest_multichannel_raw(image.get(), input_image_ptr, h0, w0, h, w);
        resize_nearest_raw(alpha.get(), input_alpha_ptr, h0, w0, h, w);
        build_level_coefficients_raw(
            alpha.get(),
            h,
            w,
            eps,
            omega,
            neighbor_weights.get(),
            inv_W.get(),
            inv_Wp1.get(),
            fg_gain.get(),
            bg_gain.get());

        const bool final_level = i_level == n_levels;
        float *currF = final_level ? F_out.data() : currF_storage.get();
        float *currB = final_level ? B_out.data() : currB_storage.get();

        resize_nearest_multichannel_raw(currF, prevF_storage.get(), prev_h, prev_w, h, w);
        resize_nearest_multichannel_raw(currB, prevB_storage.get(), prev_h, prev_w, h, w);

        for (int i_iter = 0; i_iter < n_iter; ++i_iter) {
            update_rb_half_cached_raw(
                currF,
                currB,
                image.get(),
                alpha.get(),
                neighbor_weights.get(),
                inv_W.get(),
                inv_Wp1.get(),
                fg_gain.get(),
                bg_gain.get(),
                h,
                w,
                0);
            update_rb_half_cached_raw(
                currF,
                currB,
                image.get(),
                alpha.get(),
                neighbor_weights.get(),
                inv_W.get(),
                inv_Wp1.get(),
                fg_gain.get(),
                bg_gain.get(),
                h,
                w,
                1);
        }

        if (!final_level) {
            std::swap(prevF_storage, currF_storage);
            std::swap(prevB_storage, currB_storage);
            prev_h = h;
            prev_w = w;
        }
    }
}

}  // namespace

void resize_nearest_multichannel(MutableImage dst, Image src) {
    const std::size_t h_src = src.shape(0);
    const std::size_t w_src = src.shape(1);
    const std::size_t h_dst = dst.shape(0);
    const std::size_t w_dst = dst.shape(1);

    for (std::size_t y_dst = 0; y_dst < h_dst; ++y_dst) {
        const std::size_t y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
        for (std::size_t x_dst = 0; x_dst < w_dst; ++x_dst) {
            const std::size_t x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
            for (std::size_t c = 0; c < 3; ++c) {
                dst(y_dst, x_dst, c) = src(y_src, x_src, c);
            }
        }
    }
}

void resize_nearest(MutableAlpha dst, Alpha src) {
    const std::size_t h_src = src.shape(0);
    const std::size_t w_src = src.shape(1);
    const std::size_t h_dst = dst.shape(0);
    const std::size_t w_dst = dst.shape(1);

    for (std::size_t y_dst = 0; y_dst < h_dst; ++y_dst) {
        const std::size_t y_src = std::min(h_src - 1, y_dst * h_src / h_dst);
        for (std::size_t x_dst = 0; x_dst < w_dst; ++x_dst) {
            const std::size_t x_src = std::min(w_src - 1, x_dst * w_src / w_dst);
            dst(y_dst, x_dst) = src(y_src, x_src);
        }
    }
}

void build_level_coefficients(
    Alpha alpha,
    float eps,
    float omega,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain
) {
    const std::size_t h = alpha.shape(0);
    const std::size_t w = alpha.shape(1);

    for (std::size_t y = 0; y < h; ++y) {
        for (std::size_t x = 0; x < w; ++x) {
            const float a0 = alpha(y, x);
            const float a1 = 1.0f - a0;

            float w0;
            float w1;
            float w2;
            float w3;

            if (w > 1 && h > 1 && x > 0 && x + 1 < w && y > 0 && y + 1 < h) {
                w0 = eps + omega * std::fabs(a0 - alpha(y, x - 1));
                w1 = eps + omega * std::fabs(a0 - alpha(y, x + 1));
                w2 = eps + omega * std::fabs(a0 - alpha(y - 1, x));
                w3 = eps + omega * std::fabs(a0 - alpha(y + 1, x));
            } else {
                const std::size_t x_left = x == 0 ? 0 : x - 1;
                const std::size_t x_right = std::min(w - 1, x + 1);
                const std::size_t y_up = y == 0 ? 0 : y - 1;
                const std::size_t y_down = std::min(h - 1, y + 1);

                w0 = eps + omega * std::fabs(a0 - alpha(y, x_left));
                w1 = eps + omega * std::fabs(a0 - alpha(y, x_right));
                w2 = eps + omega * std::fabs(a0 - alpha(y_up, x));
                w3 = eps + omega * std::fabs(a0 - alpha(y_down, x));
            }

            neighbor_weights(y, x, 0) = w0;
            neighbor_weights(y, x, 1) = w1;
            neighbor_weights(y, x, 2) = w2;
            neighbor_weights(y, x, 3) = w3;

            const float W = w0 + w1 + w2 + w3;
            inv_W(y, x) = 1.0f / W;
            inv_Wp1(y, x) = 1.0f / (W + 1.0f);

            const float D = W + a0 * a0 + a1 * a1;
            const float inv_D = 1.0f / D;
            fg_gain(y, x) = a0 * inv_D;
            bg_gain(y, x) = a1 * inv_D;
        }
    }
}

void update_rb_half_cached(
    MutableImage F,
    MutableImage B,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain,
    int h,
    int w,
    int color
) {
    for (int y = 0; y < h; ++y) {
        const int x_start = (color + y) % 2;
        for (int x = x_start; x < w; x += 2) {
            const float a0 = alpha(y, x);

            if (w > 1 && h > 1 && x > 0 && x + 1 < w && y > 0 && y + 1 < h) {
                const float w0 = neighbor_weights(y, x, 0);
                const float w1 = neighbor_weights(y, x, 1);
                const float w2 = neighbor_weights(y, x, 2);
                const float w3 = neighbor_weights(y, x, 3);

                const float sum_wF0 = w0 * F(y, x - 1, 0) + w1 * F(y, x + 1, 0) + w2 * F(y - 1, x, 0) +
                    w3 * F(y + 1, x, 0);
                const float sum_wF1 = w0 * F(y, x - 1, 1) + w1 * F(y, x + 1, 1) + w2 * F(y - 1, x, 1) +
                    w3 * F(y + 1, x, 1);
                const float sum_wF2 = w0 * F(y, x - 1, 2) + w1 * F(y, x + 1, 2) + w2 * F(y - 1, x, 2) +
                    w3 * F(y + 1, x, 2);
                const float sum_wB0 = w0 * B(y, x - 1, 0) + w1 * B(y, x + 1, 0) + w2 * B(y - 1, x, 0) +
                    w3 * B(y + 1, x, 0);
                const float sum_wB1 = w0 * B(y, x - 1, 1) + w1 * B(y, x + 1, 1) + w2 * B(y - 1, x, 1) +
                    w3 * B(y + 1, x, 1);
                const float sum_wB2 = w0 * B(y, x - 1, 2) + w1 * B(y, x + 1, 2) + w2 * B(y - 1, x, 2) +
                    w3 * B(y + 1, x, 2);

                write_solution(
                    F,
                    B,
                    static_cast<std::size_t>(y),
                    static_cast<std::size_t>(x),
                    a0,
                    image(y, x, 0),
                    image(y, x, 1),
                    image(y, x, 2),
                    sum_wF0,
                    sum_wF1,
                    sum_wF2,
                    sum_wB0,
                    sum_wB1,
                    sum_wB2,
                    inv_W(y, x),
                    inv_Wp1(y, x),
                    fg_gain(y, x),
                    bg_gain(y, x));
                continue;
            }

            const int x_left = x == 0 ? 0 : x - 1;
            const int x_right = x + 1 >= w ? w - 1 : x + 1;
            const int y_up = y == 0 ? 0 : y - 1;
            const int y_down = y + 1 >= h ? h - 1 : y + 1;

            const float w0 = neighbor_weights(y, x, 0);
            const float w1 = neighbor_weights(y, x, 1);
            const float w2 = neighbor_weights(y, x, 2);
            const float w3 = neighbor_weights(y, x, 3);

            const float sum_wF0 = w0 * F(y, x_left, 0) + w1 * F(y, x_right, 0) + w2 * F(y_up, x, 0) +
                w3 * F(y_down, x, 0);
            const float sum_wF1 = w0 * F(y, x_left, 1) + w1 * F(y, x_right, 1) + w2 * F(y_up, x, 1) +
                w3 * F(y_down, x, 1);
            const float sum_wF2 = w0 * F(y, x_left, 2) + w1 * F(y, x_right, 2) + w2 * F(y_up, x, 2) +
                w3 * F(y_down, x, 2);
            const float sum_wB0 = w0 * B(y, x_left, 0) + w1 * B(y, x_right, 0) + w2 * B(y_up, x, 0) +
                w3 * B(y_down, x, 0);
            const float sum_wB1 = w0 * B(y, x_left, 1) + w1 * B(y, x_right, 1) + w2 * B(y_up, x, 1) +
                w3 * B(y_down, x, 1);
            const float sum_wB2 = w0 * B(y, x_left, 2) + w1 * B(y, x_right, 2) + w2 * B(y_up, x, 2) +
                w3 * B(y_down, x, 2);

            write_solution(
                F,
                B,
                static_cast<std::size_t>(y),
                static_cast<std::size_t>(x),
                a0,
                image(y, x, 0),
                image(y, x, 1),
                image(y, x, 2),
                sum_wF0,
                sum_wF1,
                sum_wF2,
                sum_wB0,
                sum_wB1,
                sum_wB2,
                inv_W(y, x),
                inv_Wp1(y, x),
                fg_gain(y, x),
                bg_gain(y, x));
        }
    }
}

void update_rb_half_cached_from_prev_level(
    MutableImage F,
    MutableImage B,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain,
    MutableImage F_prev,
    MutableImage B_prev,
    IndexMap x_prev_map,
    IndexMap y_prev_map,
    int h,
    int w
) {
    for (int y = 0; y < h; ++y) {
        const int x_start = y % 2;
        const std::int32_t y_current_prev = y_prev_map(y);
        const std::int32_t y_up = y == 0 ? 0 : y - 1;
        const std::int32_t y_down = y + 1 >= h ? h - 1 : y + 1;
        const std::int32_t y_up_prev = y_prev_map(y_up);
        const std::int32_t y_down_prev = y_prev_map(y_down);

        for (int x = x_start; x < w; x += 2) {
            const float a0 = alpha(y, x);

            if (w > 1 && h > 1 && x > 0 && x + 1 < w && y > 0 && y + 1 < h) {
                const std::int32_t x_prev = x_prev_map(x);
                const std::int32_t x_left_prev = x_prev_map(x - 1);
                const std::int32_t x_right_prev = x_prev_map(x + 1);

                const float w0 = neighbor_weights(y, x, 0);
                const float w1 = neighbor_weights(y, x, 1);
                const float w2 = neighbor_weights(y, x, 2);
                const float w3 = neighbor_weights(y, x, 3);

                const float sum_wF0 = w0 * F_prev(y_current_prev, x_left_prev, 0) +
                    w1 * F_prev(y_current_prev, x_right_prev, 0) +
                    w2 * F_prev(y_up_prev, x_prev, 0) + w3 * F_prev(y_down_prev, x_prev, 0);
                const float sum_wF1 = w0 * F_prev(y_current_prev, x_left_prev, 1) +
                    w1 * F_prev(y_current_prev, x_right_prev, 1) +
                    w2 * F_prev(y_up_prev, x_prev, 1) + w3 * F_prev(y_down_prev, x_prev, 1);
                const float sum_wF2 = w0 * F_prev(y_current_prev, x_left_prev, 2) +
                    w1 * F_prev(y_current_prev, x_right_prev, 2) +
                    w2 * F_prev(y_up_prev, x_prev, 2) + w3 * F_prev(y_down_prev, x_prev, 2);
                const float sum_wB0 = w0 * B_prev(y_current_prev, x_left_prev, 0) +
                    w1 * B_prev(y_current_prev, x_right_prev, 0) +
                    w2 * B_prev(y_up_prev, x_prev, 0) + w3 * B_prev(y_down_prev, x_prev, 0);
                const float sum_wB1 = w0 * B_prev(y_current_prev, x_left_prev, 1) +
                    w1 * B_prev(y_current_prev, x_right_prev, 1) +
                    w2 * B_prev(y_up_prev, x_prev, 1) + w3 * B_prev(y_down_prev, x_prev, 1);
                const float sum_wB2 = w0 * B_prev(y_current_prev, x_left_prev, 2) +
                    w1 * B_prev(y_current_prev, x_right_prev, 2) +
                    w2 * B_prev(y_up_prev, x_prev, 2) + w3 * B_prev(y_down_prev, x_prev, 2);

                write_solution(
                    F,
                    B,
                    static_cast<std::size_t>(y),
                    static_cast<std::size_t>(x),
                    a0,
                    image(y, x, 0),
                    image(y, x, 1),
                    image(y, x, 2),
                    sum_wF0,
                    sum_wF1,
                    sum_wF2,
                    sum_wB0,
                    sum_wB1,
                    sum_wB2,
                    inv_W(y, x),
                    inv_Wp1(y, x),
                    fg_gain(y, x),
                    bg_gain(y, x));
                continue;
            }

            const std::int32_t x_prev = x_prev_map(x);
            const std::int32_t x_left_prev = x_prev_map(x == 0 ? 0 : x - 1);
            const std::int32_t x_right_prev = x_prev_map(x + 1 >= w ? w - 1 : x + 1);

            const std::int32_t x_left = x == 0 ? 0 : x - 1;
            const std::int32_t x_right = x + 1 >= w ? w - 1 : x + 1;

            const float w0 = neighbor_weights(y, x, 0);
            const float w1 = neighbor_weights(y, x, 1);
            const float w2 = neighbor_weights(y, x, 2);
            const float w3 = neighbor_weights(y, x, 3);

            float sum_wF0 = 0.0f;
            float sum_wF1 = 0.0f;
            float sum_wF2 = 0.0f;
            float sum_wB0 = 0.0f;
            float sum_wB1 = 0.0f;
            float sum_wB2 = 0.0f;

            if (x_left == x) {
                sum_wF0 += w0 * F_prev(y_current_prev, x_prev, 0);
                sum_wF1 += w0 * F_prev(y_current_prev, x_prev, 1);
                sum_wF2 += w0 * F_prev(y_current_prev, x_prev, 2);
                sum_wB0 += w0 * B_prev(y_current_prev, x_prev, 0);
                sum_wB1 += w0 * B_prev(y_current_prev, x_prev, 1);
                sum_wB2 += w0 * B_prev(y_current_prev, x_prev, 2);
            } else {
                sum_wF0 += w0 * F(y, x_left, 0);
                sum_wF1 += w0 * F(y, x_left, 1);
                sum_wF2 += w0 * F(y, x_left, 2);
                sum_wB0 += w0 * B(y, x_left, 0);
                sum_wB1 += w0 * B(y, x_left, 1);
                sum_wB2 += w0 * B(y, x_left, 2);
            }

            if (x_right == x) {
                sum_wF0 += w1 * F_prev(y_current_prev, x_prev, 0);
                sum_wF1 += w1 * F_prev(y_current_prev, x_prev, 1);
                sum_wF2 += w1 * F_prev(y_current_prev, x_prev, 2);
                sum_wB0 += w1 * B_prev(y_current_prev, x_prev, 0);
                sum_wB1 += w1 * B_prev(y_current_prev, x_prev, 1);
                sum_wB2 += w1 * B_prev(y_current_prev, x_prev, 2);
            } else {
                sum_wF0 += w1 * F(y, x_right, 0);
                sum_wF1 += w1 * F(y, x_right, 1);
                sum_wF2 += w1 * F(y, x_right, 2);
                sum_wB0 += w1 * B(y, x_right, 0);
                sum_wB1 += w1 * B(y, x_right, 1);
                sum_wB2 += w1 * B(y, x_right, 2);
            }

            if (y_up == y) {
                sum_wF0 += w2 * F_prev(y_current_prev, x_prev, 0);
                sum_wF1 += w2 * F_prev(y_current_prev, x_prev, 1);
                sum_wF2 += w2 * F_prev(y_current_prev, x_prev, 2);
                sum_wB0 += w2 * B_prev(y_current_prev, x_prev, 0);
                sum_wB1 += w2 * B_prev(y_current_prev, x_prev, 1);
                sum_wB2 += w2 * B_prev(y_current_prev, x_prev, 2);
            } else {
                sum_wF0 += w2 * F(y_up, x, 0);
                sum_wF1 += w2 * F(y_up, x, 1);
                sum_wF2 += w2 * F(y_up, x, 2);
                sum_wB0 += w2 * B(y_up, x, 0);
                sum_wB1 += w2 * B(y_up, x, 1);
                sum_wB2 += w2 * B(y_up, x, 2);
            }

            if (y_down == y) {
                sum_wF0 += w3 * F_prev(y_current_prev, x_prev, 0);
                sum_wF1 += w3 * F_prev(y_current_prev, x_prev, 1);
                sum_wF2 += w3 * F_prev(y_current_prev, x_prev, 2);
                sum_wB0 += w3 * B_prev(y_current_prev, x_prev, 0);
                sum_wB1 += w3 * B_prev(y_current_prev, x_prev, 1);
                sum_wB2 += w3 * B_prev(y_current_prev, x_prev, 2);
            } else {
                sum_wF0 += w3 * F(y_down, x, 0);
                sum_wF1 += w3 * F(y_down, x, 1);
                sum_wF2 += w3 * F(y_down, x, 2);
                sum_wB0 += w3 * B(y_down, x, 0);
                sum_wB1 += w3 * B(y_down, x, 1);
                sum_wB2 += w3 * B(y_down, x, 2);
            }

            write_solution(
                F,
                B,
                static_cast<std::size_t>(y),
                static_cast<std::size_t>(x),
                a0,
                image(y, x, 0),
                image(y, x, 1),
                image(y, x, 2),
                sum_wF0,
                sum_wF1,
                sum_wF2,
                sum_wB0,
                sum_wB1,
                sum_wB2,
                inv_W(y, x),
                inv_Wp1(y, x),
                fg_gain(y, x),
                bg_gain(y, x));
        }
    }
}

void update_rb_half_cached_from_prev_level_with_boundary_fallback(
    MutableImage F,
    MutableImage B,
    Image image,
    Alpha alpha,
    Coeff4 neighbor_weights,
    MutableAlpha inv_W,
    MutableAlpha inv_Wp1,
    MutableAlpha fg_gain,
    MutableAlpha bg_gain,
    MutableImage F_prev,
    MutableImage B_prev,
    IndexMap x_prev_map,
    IndexMap y_prev_map,
    int h,
    int w
) {
    for (int y = 0; y < h; ++y) {
        const int x_start = (1 + y) % 2;
        const std::int32_t y_current_prev = y_prev_map(y);
        const std::int32_t y_up = y == 0 ? 0 : y - 1;
        const std::int32_t y_down = y + 1 >= h ? h - 1 : y + 1;

        for (int x = x_start; x < w; x += 2) {
            const float a0 = alpha(y, x);

            if (w > 1 && h > 1 && x > 0 && x + 1 < w && y > 0 && y + 1 < h) {
                const float w0 = neighbor_weights(y, x, 0);
                const float w1 = neighbor_weights(y, x, 1);
                const float w2 = neighbor_weights(y, x, 2);
                const float w3 = neighbor_weights(y, x, 3);

                const float sum_wF0 = w0 * F(y, x - 1, 0) + w1 * F(y, x + 1, 0) + w2 * F(y - 1, x, 0) +
                    w3 * F(y + 1, x, 0);
                const float sum_wF1 = w0 * F(y, x - 1, 1) + w1 * F(y, x + 1, 1) + w2 * F(y - 1, x, 1) +
                    w3 * F(y + 1, x, 1);
                const float sum_wF2 = w0 * F(y, x - 1, 2) + w1 * F(y, x + 1, 2) + w2 * F(y - 1, x, 2) +
                    w3 * F(y + 1, x, 2);
                const float sum_wB0 = w0 * B(y, x - 1, 0) + w1 * B(y, x + 1, 0) + w2 * B(y - 1, x, 0) +
                    w3 * B(y + 1, x, 0);
                const float sum_wB1 = w0 * B(y, x - 1, 1) + w1 * B(y, x + 1, 1) + w2 * B(y - 1, x, 1) +
                    w3 * B(y + 1, x, 1);
                const float sum_wB2 = w0 * B(y, x - 1, 2) + w1 * B(y, x + 1, 2) + w2 * B(y - 1, x, 2) +
                    w3 * B(y + 1, x, 2);

                write_solution(
                    F,
                    B,
                    static_cast<std::size_t>(y),
                    static_cast<std::size_t>(x),
                    a0,
                    image(y, x, 0),
                    image(y, x, 1),
                    image(y, x, 2),
                    sum_wF0,
                    sum_wF1,
                    sum_wF2,
                    sum_wB0,
                    sum_wB1,
                    sum_wB2,
                    inv_W(y, x),
                    inv_Wp1(y, x),
                    fg_gain(y, x),
                    bg_gain(y, x));
                continue;
            }

            const int x_left = x == 0 ? 0 : x - 1;
            const int x_right = x + 1 >= w ? w - 1 : x + 1;
            const int x_current_prev = x_prev_map(x);
            const std::int32_t y_up_prev = y_prev_map(y_up);
            const std::int32_t y_down_prev = y_prev_map(y_down);

            const float w0 = neighbor_weights(y, x, 0);
            const float w1 = neighbor_weights(y, x, 1);
            const float w2 = neighbor_weights(y, x, 2);
            const float w3 = neighbor_weights(y, x, 3);

            float sum_wF0 = 0.0f;
            float sum_wF1 = 0.0f;
            float sum_wF2 = 0.0f;
            float sum_wB0 = 0.0f;
            float sum_wB1 = 0.0f;
            float sum_wB2 = 0.0f;

            // Left neighbor.
            if (x_left == x) {
                sum_wF0 += w0 * F_prev(y_current_prev, x_current_prev, 0);
                sum_wF1 += w0 * F_prev(y_current_prev, x_current_prev, 1);
                sum_wF2 += w0 * F_prev(y_current_prev, x_current_prev, 2);
                sum_wB0 += w0 * B_prev(y_current_prev, x_current_prev, 0);
                sum_wB1 += w0 * B_prev(y_current_prev, x_current_prev, 1);
                sum_wB2 += w0 * B_prev(y_current_prev, x_current_prev, 2);
            } else {
                sum_wF0 += w0 * F(y, x_left, 0);
                sum_wF1 += w0 * F(y, x_left, 1);
                sum_wF2 += w0 * F(y, x_left, 2);
                sum_wB0 += w0 * B(y, x_left, 0);
                sum_wB1 += w0 * B(y, x_left, 1);
                sum_wB2 += w0 * B(y, x_left, 2);
            }

            // Right neighbor.
            if (x_right == x) {
                sum_wF0 += w1 * F_prev(y_current_prev, x_current_prev, 0);
                sum_wF1 += w1 * F_prev(y_current_prev, x_current_prev, 1);
                sum_wF2 += w1 * F_prev(y_current_prev, x_current_prev, 2);
                sum_wB0 += w1 * B_prev(y_current_prev, x_current_prev, 0);
                sum_wB1 += w1 * B_prev(y_current_prev, x_current_prev, 1);
                sum_wB2 += w1 * B_prev(y_current_prev, x_current_prev, 2);
            } else {
                sum_wF0 += w1 * F(y, x_right, 0);
                sum_wF1 += w1 * F(y, x_right, 1);
                sum_wF2 += w1 * F(y, x_right, 2);
                sum_wB0 += w1 * B(y, x_right, 0);
                sum_wB1 += w1 * B(y, x_right, 1);
                sum_wB2 += w1 * B(y, x_right, 2);
            }

            // Up neighbor.
            if (y_up == y) {
                sum_wF0 += w2 * F_prev(y_current_prev, x_current_prev, 0);
                sum_wF1 += w2 * F_prev(y_current_prev, x_current_prev, 1);
                sum_wF2 += w2 * F_prev(y_current_prev, x_current_prev, 2);
                sum_wB0 += w2 * B_prev(y_current_prev, x_current_prev, 0);
                sum_wB1 += w2 * B_prev(y_current_prev, x_current_prev, 1);
                sum_wB2 += w2 * B_prev(y_current_prev, x_current_prev, 2);
            } else {
                sum_wF0 += w2 * F(y_up, x, 0);
                sum_wF1 += w2 * F(y_up, x, 1);
                sum_wF2 += w2 * F(y_up, x, 2);
                sum_wB0 += w2 * B(y_up, x, 0);
                sum_wB1 += w2 * B(y_up, x, 1);
                sum_wB2 += w2 * B(y_up, x, 2);
            }

            // Down neighbor.
            if (y_down == y) {
                sum_wF0 += w3 * F_prev(y_current_prev, x_current_prev, 0);
                sum_wF1 += w3 * F_prev(y_current_prev, x_current_prev, 1);
                sum_wF2 += w3 * F_prev(y_current_prev, x_current_prev, 2);
                sum_wB0 += w3 * B_prev(y_current_prev, x_current_prev, 0);
                sum_wB1 += w3 * B_prev(y_current_prev, x_current_prev, 1);
                sum_wB2 += w3 * B_prev(y_current_prev, x_current_prev, 2);
            } else {
                sum_wF0 += w3 * F(y_down, x, 0);
                sum_wF1 += w3 * F(y_down, x, 1);
                sum_wF2 += w3 * F(y_down, x, 2);
                sum_wB0 += w3 * B(y_down, x, 0);
                sum_wB1 += w3 * B(y_down, x, 1);
                sum_wB2 += w3 * B(y_down, x, 2);
            }

            write_solution(
                F,
                B,
                static_cast<std::size_t>(y),
                static_cast<std::size_t>(x),
                a0,
                image(y, x, 0),
                image(y, x, 1),
                image(y, x, 2),
                sum_wF0,
                sum_wF1,
                sum_wF2,
                sum_wB0,
                sum_wB1,
                sum_wB2,
                inv_W(y, x),
                inv_Wp1(y, x),
                fg_gain(y, x),
                bg_gain(y, x));
        }
    }
}

NB_MODULE(_cpu_impl, m) {
    m.def(
        "estimate_fb_ml",
        &estimate_fb_ml,
        nb::arg("F_out"),
        nb::arg("B_out"),
        nb::arg("input_image"),
        nb::arg("input_alpha"),
        nb::arg("regularization"),
        nb::arg("gradient_weight"),
        nb::arg("n_small_iterations"),
        nb::arg("n_big_iterations"),
        nb::arg("small_size"));
    m.def(
        "estimate_fb_ml_u8",
        &estimate_fb_ml_u8,
        nb::arg("F_out"),
        nb::arg("B_out"),
        nb::arg("input_image"),
        nb::arg("input_alpha"),
        nb::arg("regularization"),
        nb::arg("gradient_weight"),
        nb::arg("n_small_iterations"),
        nb::arg("n_big_iterations"),
        nb::arg("small_size"));
    m.def("_resize_nearest_multichannel", &resize_nearest_multichannel, nb::arg("dst"), nb::arg("src"));
    m.def("_resize_nearest", &resize_nearest, nb::arg("dst"), nb::arg("src"));
    m.def(
        "_build_level_coefficients",
        &build_level_coefficients,
        nb::arg("alpha"),
        nb::arg("eps"),
        nb::arg("omega"),
        nb::arg("neighbor_weights"),
        nb::arg("inv_W"),
        nb::arg("inv_Wp1"),
        nb::arg("fg_gain"),
        nb::arg("bg_gain"));
    m.def(
        "_update_rb_half_cached",
        &update_rb_half_cached,
        nb::arg("F"),
        nb::arg("B"),
        nb::arg("image"),
        nb::arg("alpha"),
        nb::arg("neighbor_weights"),
        nb::arg("inv_W"),
        nb::arg("inv_Wp1"),
        nb::arg("fg_gain"),
        nb::arg("bg_gain"),
        nb::arg("h"),
        nb::arg("w"),
        nb::arg("color"));
    m.def(
        "_update_rb_half_cached_from_prev_level",
        &update_rb_half_cached_from_prev_level,
        nb::arg("F"),
        nb::arg("B"),
        nb::arg("image"),
        nb::arg("alpha"),
        nb::arg("neighbor_weights"),
        nb::arg("inv_W"),
        nb::arg("inv_Wp1"),
        nb::arg("fg_gain"),
        nb::arg("bg_gain"),
        nb::arg("F_prev"),
        nb::arg("B_prev"),
        nb::arg("x_prev_map"),
        nb::arg("y_prev_map"),
        nb::arg("h"),
        nb::arg("w"));
    m.def(
        "_update_rb_half_cached_from_prev_level_with_boundary_fallback",
        &update_rb_half_cached_from_prev_level_with_boundary_fallback,
        nb::arg("F"),
        nb::arg("B"),
        nb::arg("image"),
        nb::arg("alpha"),
        nb::arg("neighbor_weights"),
        nb::arg("inv_W"),
        nb::arg("inv_Wp1"),
        nb::arg("fg_gain"),
        nb::arg("bg_gain"),
        nb::arg("F_prev"),
        nb::arg("B_prev"),
        nb::arg("x_prev_map"),
        nb::arg("y_prev_map"),
        nb::arg("h"),
        nb::arg("w"));
}
