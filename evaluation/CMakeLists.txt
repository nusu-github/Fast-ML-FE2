cmake_minimum_required(VERSION 3.15...3.30)
project(${SKBUILD_PROJECT_NAME} LANGUAGES CXX)

if(CMAKE_VERSION VERSION_LESS 3.18)
    set(DEV_MODULE Development)
else()
    set(DEV_MODULE Development.Module)
endif()

find_package(Python
    REQUIRED COMPONENTS Interpreter ${DEV_MODULE}
    OPTIONAL_COMPONENTS Development.SABIModule
)

execute_process(
    COMMAND "${Python_EXECUTABLE}" -m nanobind --cmake_dir
    OUTPUT_STRIP_TRAILING_WHITESPACE
    OUTPUT_VARIABLE nanobind_ROOT
)

find_package(nanobind CONFIG REQUIRED)

nanobind_add_module(_cpu_impl cpp/cpu_impl.cpp)
target_compile_features(_cpu_impl PUBLIC cxx_std_17)
set_target_properties(_cpu_impl PROPERTIES CXX_EXTENSIONS OFF)

install(TARGETS _cpu_impl LIBRARY DESTINATION fastmlfe2_eval/estimator)
