//
// Created by antti on 23.08.19.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <SMTConfig.h>
#include <LAScore.h>
#include <cstdlib>
#include <string>

class BestLitBufTest: public ::testing::Test {
public:
    BestLitBufTest() {}
};

TEST_F(BestLitBufTest, test_UnitLookahead) {
    vec<lbool> assigns;
    for (int i = 0; i < 10; i++)
        assigns.push(l_Undef);

    LABestLitBuf<LookaheadScoreClassic::ExVal> buf(2, assigns, true, 1);

    LookaheadScoreClassic::ExVal v1(1,1,1);
    Lit l1 = mkLit(0, true);
    LookaheadScoreClassic::ExVal v2(2, 1, 1);
    Lit l2 = mkLit(1, true);
    LookaheadScoreClassic::ExVal v3(1, 2, 1);
    Lit l3 = mkLit(2, true);
    LookaheadScoreClassic::ExVal v4(2, 2, 1);
    Lit l4 = mkLit(3, true);
    LookaheadScoreClassic::ExVal v5(1, 1, 2);
    Lit l5 = mkLit(4, true);
    LookaheadScoreClassic::ExVal v6(2, 1, 1);
    Lit l6 = mkLit(5, true);

    buf.insert(l1, v1);
    ASSERT_EQ(buf.getLit(0), l1);
    buf.insert(l2, v2);
    ASSERT_EQ(buf.getLit(1), l2);
    buf.insert(l3, v3);
    ASSERT_EQ(buf.getLit(0), l3);
    buf.insert(l4, v4);
    ASSERT_TRUE(buf.getLit(0) == l3 || buf.getLit(0) == l4);
    ASSERT_TRUE(buf.getLit(1) == l3 || buf.getLit(1) == l4);
    ASSERT_TRUE(buf.getLit(0) != buf.getLit(1));
    buf.insert(l5,v5);
    ASSERT_TRUE(buf.getLit(0) == l5 || buf.getLit(1) == l5);
    buf.insert(l6,v6);
    ASSERT_TRUE(buf.getLit(0) != l6 && buf.getLit(1) != l6);

//    for (int i = 0; i < 100; i++) {
//        Var v = rand() % assigns.size();
//        bool p = rand() % 2;
//        Lit l = mkLit(v, p);
//
//        LookaheadScoreClassic::ExVal val(rand() % 10, rand() % 10, 1);
//        std::cout << "inserting lit " << l.x << " val " << val.str() << endl;
//        buf.insert(l, val);
//        std::cout << buf.str();
//    }
}