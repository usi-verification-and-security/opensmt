include(FetchContent)

FetchContent_Declare(
    googlebenchmark
    GIT_REPOSITORY https://github.com/google/benchmark.git
    GIT_TAG v1.7.0
)

FetchContent_GetProperties(googlebenchmark)

if (NOT benchmark_POPULATED)
  FetchContent_Populate(googlebenchmark)
  set(BENCHMARK_ENABLE_GTEST_TESTS OFF CACHE INTERNAL "")
  set(BENCHMARK_ENABLE_INSTALL OFF CACHE INTERNAL "")
  set(BENCHMARK_ENABLE_TESTING OFF CACHE INTERNAL "")
  add_subdirectory(${googlebenchmark_SOURCE_DIR} ${googlebenchmark_BINARY_DIR} EXCLUDE_FROM_ALL)
endif ()

add_subdirectory(performance)
