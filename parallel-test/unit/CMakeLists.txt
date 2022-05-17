include(GoogleTest)

add_executable(SolverBranchBoundary)
target_sources(SolverBranchBoundary PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_SolverBranchBoundary.cc")
target_link_libraries(SolverBranchBoundary PUBLIC OpenSMT-splitter-static gtest gtest_main)
gtest_add_tests(TARGET SolverBranchBoundary)