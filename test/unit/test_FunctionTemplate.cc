//
// Created by Antti on 01.06.21.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <SMTConfig.h>
#include <Opensmt.h>

class TemplateTest : public ::testing::Test {
protected:
    Logic logic;
    SRef s;
    PTRef a1;
    PTRef a2;
    PTRef b1;
    PTRef b2;
public:
    TemplateTest()
            : logic{opensmt::Logic_t::QF_UF}
            , s(logic.declareUninterpretedSort("S"))
            , a1(logic.mkVar(s, "a1"))
            , a2(logic.mkVar(s, "a2"))
            , b1(logic.mkVar(s, "b1"))
            , b2(logic.mkVar(s, "b2"))
    {}
};

TEST_F(TemplateTest, test_functionSignature) {
    FunctionSignature fs("f", {a1, a2}, s);
    EXPECT_EQ(fs.getName(), "f");
    EXPECT_EQ(fs.getRetSort(), s);
    const auto & args = fs.getArgs();
    EXPECT_EQ(args[0], a1);
    EXPECT_EQ(args[1], a2);
}

TEST_F(TemplateTest, test_functionTemplate) {
    TemplateFunction templateFunction("f", {a1, a2}, s, a1);
    EXPECT_EQ(templateFunction.getName(), "f");
    EXPECT_EQ(templateFunction.getRetSort(), s);
    EXPECT_EQ(templateFunction.getBody(), a1);
    const auto & args = templateFunction.getArgs();
    EXPECT_EQ(args[0], a1);
    EXPECT_EQ(args[1], a2);
    templateFunction.updateBody(a2);
    EXPECT_EQ(templateFunction.getBody(), a2);

    TemplateFunction tf2(FunctionSignature("g", {a1, a2}, s), a2);
    EXPECT_EQ(tf2.getName(), "g");
    EXPECT_EQ(tf2.getRetSort(), s);
    EXPECT_EQ(tf2.getBody(), a2);
    const auto & args2 = tf2.getArgs();
    EXPECT_EQ(args2[0], a1);
    EXPECT_EQ(args2[1], a2);
    tf2.updateBody(a1);
    EXPECT_EQ(tf2.getBody(), a1);

    tf2 = std::move(templateFunction);
    EXPECT_EQ(tf2.getName(), "f");
    EXPECT_EQ(tf2.getRetSort(), s);
    EXPECT_EQ(tf2.getBody(), a2);
    const auto & args3 = tf2.getArgs();
    EXPECT_EQ(args3[0], a1);
    EXPECT_EQ(args3[1], a2);

    TemplateFunction tf3(tf2);
    EXPECT_EQ(tf3.getName(), tf2.getName());
    EXPECT_EQ(tf3.getRetSort(), tf2.getRetSort());
    EXPECT_EQ(tf3.getBody(), tf2.getBody());
    EXPECT_EQ(tf3.getArgs()[0], tf2.getArgs()[0]);
    EXPECT_EQ(tf3.getArgs()[1], tf2.getArgs()[1]);

    TemplateFunction tf4(std::move(tf2));
    EXPECT_EQ(tf3.getName(), tf4.getName());
    EXPECT_EQ(tf3.getRetSort(), tf4.getRetSort());
    EXPECT_EQ(tf3.getBody(), tf4.getBody());
    EXPECT_EQ(tf3.getArgs()[0], tf4.getArgs()[0]);
    EXPECT_EQ(tf3.getArgs()[1], tf4.getArgs()[1]);
}

TEST_F(TemplateTest, test_template) {
    FunctionSignature fs("f", {a1, a2}, s);
    TemplateFunction temp("f", {a1, a2}, logic.getSort_bool(), logic.mkEq(a1, a2));
    ASSERT_ANY_THROW(logic.instantiateFunctionTemplate(temp, {}));
    ASSERT_ANY_THROW(logic.instantiateFunctionTemplate(temp, {a1, logic.getTerm_true()}));
    PTRef res = logic.instantiateFunctionTemplate(temp, {b1,b2});
    PTRef ref = logic.mkEq(b1, b2);
    ASSERT_EQ(res, ref);
}