#include "fastmlfe2_ffi.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

struct GrayImage {
  int width;
  int height;
  int stride;
  std::vector<float> data;
};

std::string read_token(std::istream &in) {
  std::string token;
  char ch = '\0';
  while (in.get(ch)) {
    if (std::isspace(static_cast<unsigned char>(ch))) {
      continue;
    }
    if (ch == '#') {
      std::string ignored;
      std::getline(in, ignored);
      continue;
    }
    token.push_back(ch);
    break;
  }
  while (in.get(ch)) {
    if (std::isspace(static_cast<unsigned char>(ch))) {
      break;
    }
    token.push_back(ch);
  }
  if (token.empty()) {
    throw std::runtime_error("unexpected end of PGM header");
  }
  return token;
}

GrayImage read_pgm(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in) {
    throw std::runtime_error("failed to open input: " + path);
  }

  const std::string magic = read_token(in);
  if (magic != "P5") {
    throw std::runtime_error("only binary PGM (P5) is supported: " + path);
  }

  const int width = std::stoi(read_token(in));
  const int height = std::stoi(read_token(in));
  const int maxval = std::stoi(read_token(in));
  if (width <= 0 || height <= 0 || maxval <= 0 || maxval > 255) {
    throw std::runtime_error("unsupported PGM header: " + path);
  }

  GrayImage image{width, height, width, std::vector<float>(
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height))};
  std::vector<unsigned char> bytes(image.data.size());
  in.read(reinterpret_cast<char *>(bytes.data()),
          static_cast<std::streamsize>(bytes.size()));
  if (in.gcount() != static_cast<std::streamsize>(bytes.size())) {
    throw std::runtime_error("truncated PGM payload: " + path);
  }

  const float scale = 1.0f / static_cast<float>(maxval);
  for (std::size_t i = 0; i < bytes.size(); ++i) {
    image.data[i] = static_cast<float>(bytes[i]) * scale;
  }
  return image;
}

void write_pgm(const std::string &path, const GrayImage &image) {
  std::ofstream out(path, std::ios::binary);
  if (!out) {
    throw std::runtime_error("failed to open output: " + path);
  }
  out << "P5\n" << image.width << " " << image.height << "\n255\n";

  std::vector<unsigned char> bytes(
      static_cast<std::size_t>(image.width) * static_cast<std::size_t>(image.height));
  for (int y = 0; y < image.height; ++y) {
    for (int x = 0; x < image.width; ++x) {
      const float value =
          image.data[static_cast<std::size_t>(y) * static_cast<std::size_t>(image.stride) +
                     static_cast<std::size_t>(x)];
      const float clamped = std::clamp(value, 0.0f, 1.0f);
      bytes[static_cast<std::size_t>(y) * static_cast<std::size_t>(image.width) +
            static_cast<std::size_t>(x)] =
          static_cast<unsigned char>(clamped * 255.0f + 0.5f);
    }
  }
  out.write(reinterpret_cast<const char *>(bytes.data()),
            static_cast<std::streamsize>(bytes.size()));
}

GrayImage make_image(int width, int height) {
  return GrayImage{
      width,
      height,
      width,
      std::vector<float>(static_cast<std::size_t>(width) * static_cast<std::size_t>(height), 0.0f)};
}

GrayImage resize_to_match(const GrayImage &src, int width, int height) {
  if (src.width == width && src.height == height) {
    return src;
  }
  GrayImage dst = make_image(width, height);
  const int rc = fastmlfe2_resize_float_gray(
      src.data.data(), src.width, src.height, src.stride,
      dst.data.data(), dst.width, dst.height, dst.stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    throw std::runtime_error("resize_float_gray failed with status " + std::to_string(rc));
  }
  return dst;
}

void clamp_image(GrayImage &image) {
  const int rc = fastmlfe2_clamp01_gray(
      image.data.data(), image.width, image.height, image.stride);
  if (rc != FASTMLFE2_STATUS_OK) {
    throw std::runtime_error("clamp01_gray failed with status " + std::to_string(rc));
  }
}

void usage(const char *argv0) {
  std::cerr
      << "usage: " << argv0
      << " image.pgm alpha.pgm fg_init.pgm bg_init.pgm out_fg.pgm out_bg.pgm"
      << " iterations eps_r omega\n";
}

}  // namespace

int main(int argc, char **argv) {
  if (argc != 10) {
    usage(argv[0]);
    return 1;
  }

  try {
    const std::string image_path = argv[1];
    const std::string alpha_path = argv[2];
    const std::string fg_path = argv[3];
    const std::string bg_path = argv[4];
    const std::string out_fg_path = argv[5];
    const std::string out_bg_path = argv[6];
    const int iterations = std::stoi(argv[7]);
    const float eps_r = std::stof(argv[8]);
    const float omega = std::stof(argv[9]);

    if (iterations < 0) {
      throw std::runtime_error("iterations must be nonnegative");
    }

    GrayImage image = read_pgm(image_path);
    GrayImage alpha = read_pgm(alpha_path);
    if (alpha.width != image.width || alpha.height != image.height) {
      throw std::runtime_error("alpha image must match input image dimensions");
    }

    GrayImage fg = resize_to_match(read_pgm(fg_path), image.width, image.height);
    GrayImage bg = resize_to_match(read_pgm(bg_path), image.width, image.height);
    GrayImage fg_out = make_image(image.width, image.height);
    GrayImage bg_out = make_image(image.width, image.height);

    for (int iter = 0; iter < iterations; ++iter) {
      const int rc = fastmlfe2_reference_refine_gray_single_pass(
          image.data.data(), alpha.data.data(), fg.data.data(), bg.data.data(),
          fg_out.data.data(), bg_out.data.data(),
          image.width, image.height, image.stride, eps_r, omega);
      if (rc != FASTMLFE2_STATUS_OK) {
        throw std::runtime_error(
            "reference_refine_gray_single_pass failed with status " + std::to_string(rc));
      }
      clamp_image(fg_out);
      clamp_image(bg_out);
      std::swap(fg.data, fg_out.data);
      std::swap(bg.data, bg_out.data);
    }

    write_pgm(out_fg_path, fg);
    write_pgm(out_bg_path, bg);
    return 0;
  } catch (const std::exception &ex) {
    std::cerr << "ffi-runner: " << ex.what() << "\n";
    return 2;
  }
}
