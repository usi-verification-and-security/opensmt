add_executable(RationalEfficiencyBenchmark)
target_sources(RationalEfficiencyBenchmark
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/perf_RationalEfficiency.cc"
        )

target_link_libraries(RationalEfficiencyBenchmark OpenSMT benchmark::benchmark benchmark_main)
