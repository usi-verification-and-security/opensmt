include(GoogleTest)
add_executable(LRATest)
target_sources(LRATest 
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Rationals.cpp"
#    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Delta.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Matrix.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Polynomial.cpp"
    )

target_link_libraries(LRATest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET LRATest)

add_executable(RewritingTest)
target_sources(RewritingTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_simplifyAssignment.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Dominators.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Rewriting.cc"
    )

target_link_libraries(RewritingTest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET RewritingTest)

add_executable(TheorySimplificationsTest)
target_sources(TheorySimplificationsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TheorySimplifications.cc"
    )

target_link_libraries(TheorySimplificationsTest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET TheorySimplificationsTest)

add_executable(EGraphTest)
target_sources(EGraphTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Egraph.cc"
    )

target_link_libraries(EGraphTest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET EGraphTest)

add_executable(LATest)
target_sources(LATest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Lookahead.cpp"
    )

target_link_libraries(LATest OpenSMT gtest gtest_main)


gtest_add_tests(TARGET LATest)

add_executable(SimplexTest)
target_sources(SimplexTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Simplex.cc"
    )

target_link_libraries(SimplexTest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET SimplexTest)

add_executable(HermiteTest)
target_sources(HermiteTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_HNF.cc"
    )

target_link_libraries(HermiteTest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET HermiteTest)

add_executable(LIACutTest)
target_sources(LIACutTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LIACutSolver.cpp"
    )

target_link_libraries(LIACutTest OpenSMT gtest gtest_main)

gtest_add_tests(TARGET LIACutTest)

add_executable(STPSolverTest)
target_sources(STPSolverTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_IDLSolver.cpp"
    )
target_link_libraries(STPSolverTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET STPSolverTest)

add_executable(SubstitutionsTest)
target_sources(SubstitutionsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_SubstitutionBreaker.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LIASubstitutionsRegression.cc"
    )

target_link_libraries(SubstitutionsTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET SubstitutionsTest)

add_executable(LogicMkTermsTest)
target_sources(LogicMkTermsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LogicMkTerms.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LIALogicMkTerms.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LRALogicMkTerms.cc"
    )

target_link_libraries(LogicMkTermsTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET LogicMkTermsTest)

add_executable(BoundTest)
target_sources(BoundTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Bounds.cc"
    )

target_link_libraries(BoundTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET BoundTest)

add_executable(ModelTest)
target_sources(ModelTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Model.cc"
    )

target_link_libraries(ModelTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET ModelTest)

add_executable(IteTest)
target_sources(IteTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Ites.cc"
        )


target_link_libraries(IteTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET IteTest)

add_executable(LIAStrengtheningTest)
target_sources(LIAStrengtheningTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LIAStrengthening.cc"
        )


target_link_libraries(LIAStrengtheningTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET LIAStrengtheningTest)

add_executable(InterpolationTest)
target_sources(InterpolationTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_UFInterpolation.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LRAInterpolation.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LIAInterpolation.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_ResolutionProofInterpolation.cc"
    )

target_link_libraries(InterpolationTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET InterpolationTest)

add_executable(ExplainTest)
target_sources(ExplainTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Explain.cc"
        )

target_link_libraries(ExplainTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET ExplainTest)

add_executable(EnodeStoreTest)
target_sources(EnodeStoreTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_EnodeStore.cc"
        )

target_link_libraries(EnodeStoreTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET EnodeStoreTest)

add_executable(FunctionTemplateTest)
target_sources(FunctionTemplateTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_FunctionTemplate.cc"
        )

target_link_libraries(FunctionTemplateTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET FunctionTemplateTest)

add_executable(ProofTest)
target_sources(ProofTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Proof.cc"
        )

target_link_libraries(ProofTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET ProofTest)

add_executable(SplitTest)
target_sources(SplitTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Splitting.cc"
        )

target_link_libraries(SplitTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET SplitTest)

add_executable(NumberParserTest)
target_sources(NumberParserTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_NumberParser.cc"
        )

target_link_libraries(NumberParserTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET NumberParserTest)


add_executable(TermTypecheckingTest)
target_sources(TermTypecheckingTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TermTypechecking.cc"
        )

target_link_libraries(TermTypecheckingTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET TermTypecheckingTest)

add_executable(ArithLogicApiTest)
target_sources(ArithLogicApiTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_ArithLogicApi.cc"
        )

target_link_libraries(ArithLogicApiTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET ArithLogicApiTest)

add_executable(TermsTest)
target_sources(TermsTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Sorts.cc"
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Visitors.cc"
        )

target_link_libraries(TermsTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET TermsTest)

add_executable(LASolverIncrementalityTest)
target_sources(LASolverIncrementalityTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LASolverIncrementality.cc"
        )

target_link_libraries(LASolverIncrementalityTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET LASolverIncrementalityTest)

add_executable(NameProtectionTest)
target_sources(NameProtectionTest
        PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_NameProtection.cc"
        )

target_link_libraries(NameProtectionTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET NameProtectionTest)

add_executable(SATSolverTypesTest)
target_sources(SATSolverTypesTest
PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_SATSolverTypes.cc"
)

target_link_libraries(SATSolverTypesTest OpenSMT gtest gtest_main)
gtest_add_tests(TARGET SATSolverTypesTest)