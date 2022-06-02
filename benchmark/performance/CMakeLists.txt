add_executable(RationalEfficiencyBenchmark)
target_sources(RationalEfficiencyBenchmark
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/perf_RationalEfficiency.cc"
        )

target_link_libraries(RationalEfficiencyBenchmark OpenSMT benchmark::benchmark benchmark_main)

add_executable(MakeTermsBenchmarkSmall)
target_sources(MakeTermsBenchmarkSmall
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/perf_mkTermsSmallConj.cc"
        )

target_link_libraries(MakeTermsBenchmarkSmall OpenSMT benchmark::benchmark benchmark_main)

add_executable(MakeTermsBenchmarkBig)
target_sources(MakeTermsBenchmarkBig
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/perf_mkTermsBigConj.cc"
        )

target_link_libraries(MakeTermsBenchmarkBig OpenSMT benchmark::benchmark benchmark_main)
