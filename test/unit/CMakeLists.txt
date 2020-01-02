include(GoogleTest)
add_executable(LRATest)
target_sources(LRATest 
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Rationals.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Delta.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Matrix.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Polynomial.cpp"
    )

target_link_libraries(LRATest api_static gtest gtest_main)

gtest_add_tests(TARGET LRATest)

add_executable(RewritingTest)
target_sources(RewritingTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_simplifyAssignment.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Dominators.cpp"
    )

target_link_libraries(RewritingTest api_static gtest gtest_main)

gtest_add_tests(TARGET RewritingTest)

add_executable(ExpressionsTest)
target_sources(ExpressionsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_ArithmeticExpressions.cpp"
    )

target_link_libraries(ExpressionsTest api_static gtest gtest_main)

gtest_add_tests(TARGET ExpressionsTest)

add_executable(TheorySimplificationsTest)
target_sources(TheorySimplificationsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TheorySimplifications.cpp"
    )

target_link_libraries(TheorySimplificationsTest api_static gtest gtest_main)

gtest_add_tests(TARGET TheorySimplificationsTest)

add_executable(EGraphTest)
target_sources(EGraphTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Egraph.cpp"
    )

target_link_libraries(EGraphTest api_static gtest gtest_main)

gtest_add_tests(TARGET EGraphTest)

add_executable(LATest)
target_sources(LATest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Lookahead.cpp"
    )

target_link_libraries(LATest api_static gtest gtest_main)


gtest_add_tests(TARGET LATest)

add_executable(SimplexTest)
target_sources(SimplexTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Simplex.cpp"
    )

target_link_libraries(SimplexTest api_static gtest gtest_main)

gtest_add_tests(TARGET SimplexTest)

add_executable(HermiteTest)
target_sources(HermiteTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_HNF.cpp"
    )

target_link_libraries(HermiteTest api_static gtest gtest_main)

gtest_add_tests(TARGET HermiteTest)

add_executable(LIACutTest)
target_sources(LIACutTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LIACutSolver.cpp"
    )

target_link_libraries(LIACutTest api_static gtest gtest_main)

gtest_add_tests(TARGET LIACutTest)

add_executable(STPSolverTest)
target_sources(STPSolverTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_STPSolver.cpp"
    )
target_link_libraries(STPSolverTest api_static gtest gtest_main)
gtest_add_tests(TARGET STPSolverTest)