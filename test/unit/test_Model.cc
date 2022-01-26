//
// Created by Martin Blicha on 14.06.20.
//

#include <gtest/gtest.h>
#include <ArithLogic.h>
#include <SMTConfig.h>
#include <Model.h>
#include <ModelBuilder.h>
#include <Opensmt.h>

#include <memory>
#include <Substitutor.h>

class UFModelTest : public ::testing::Test {
protected:
    UFModelTest(): logic{opensmt::Logic_t::QF_UF} {}
    virtual void SetUp() {
        S = logic.declareUninterpretedSort("U");
        x = logic.mkVar(S, "x");
        y = logic.mkVar(S, "y");
        z = logic.mkVar(S, "z");
        f_sym = logic.declareFun("f", S, {S, S});
        f = logic.mkUninterpFun(f_sym, {x, y});

        v0 = logic.mkConst(S, "@0");
        v1 = logic.mkConst(S, "@1");

        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
    }
    SMTConfig config;
    Logic logic;

    SRef S;

    PTRef x;
    PTRef y;
    PTRef z;
    PTRef f;
    PTRef a;
    PTRef b;

    PTRef v0;
    PTRef v1;

    SymRef f_sym;

    std::unique_ptr<Model> getModel() {
        Model::Evaluation eval {
                std::make_pair(x, v0),
                std::make_pair(y, v0),
                std::make_pair(z, v1),
                std::make_pair(a, logic.getTerm_true()),
                std::make_pair(b, logic.getTerm_false()),
        };
        Model::SymbolDefinition symDef {
            std::make_pair(f_sym, TemplateFunction("f", {x, y}, S, logic.mkIte(logic.mkEq(x, v1), v0, v1)))
        };
        return std::unique_ptr<Model>(new Model(logic, eval, symDef));
    }
};

class UFModelBuilderTest : public ::testing::Test {
protected:
    UFModelBuilderTest(): logic{opensmt::Logic_t::QF_UF} {}
    virtual void SetUp() {
        S = logic.declareUninterpretedSort("U");
        x = logic.mkVar(S, "x");
        y = logic.mkVar(S, "y");
        z = logic.mkVar(S, "z");
        f_sym = logic.declareFun("f", S, {S, S});
        f = logic.mkUninterpFun(f_sym, {x, y});

        v0 = logic.mkConst(S, "@0");
        v1 = logic.mkConst(S, "@1");

        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
    }
    SMTConfig config;
    Logic logic;

    SRef S;

    PTRef x;
    PTRef y;
    PTRef z;
    PTRef f;
    PTRef a;
    PTRef b;

    PTRef v0;
    PTRef v1;

    SymRef f_sym;

    std::unique_ptr<Model> getModel() {
        ModelBuilder mb(logic);
        Model::Evaluation eval {
                std::make_pair(x, v0),
                std::make_pair(y, v0),
                std::make_pair(z, v1),
                std::make_pair(a, logic.getTerm_true()),
                std::make_pair(b, logic.getTerm_false()),
        };
        mb.addToTheoryFunction(f_sym, {v0, v0}, v0);
        mb.addVarValues(eval.begin(), eval.end());
        return mb.build();
    }
};

TEST_F(UFModelTest, test_varAndFunctionEvaluation) {
    auto model = getModel();
    EXPECT_EQ(model->evaluate(x), v0);
    EXPECT_EQ(model->evaluate(y), v0);
    EXPECT_EQ(model->evaluate(z), v1);
    EXPECT_EQ(model->evaluate(f), v1);
    EXPECT_EQ(model->evaluate(logic.mkUninterpFun(f_sym, {logic.mkUninterpFun(f_sym, {x, y}), x})), v0);
    EXPECT_EQ(model->evaluate(a), logic.getTerm_true());
    EXPECT_EQ(model->evaluate(b), logic.getTerm_false());
}

TEST_F(UFModelBuilderTest, test_modelBuilderVarAndFunction) {
    auto model = getModel();
    EXPECT_EQ(model->evaluate(x), v0);
    EXPECT_EQ(model->evaluate(y), v0);
    EXPECT_EQ(model->evaluate(z), v1);
    EXPECT_EQ(model->evaluate(f), v0);
    EXPECT_EQ(model->evaluate(logic.mkUninterpFun(f_sym, {logic.mkUninterpFun(f_sym, {x, y}), x})), v0);
    EXPECT_EQ(model->evaluate(a), logic.getTerm_true());
    EXPECT_EQ(model->evaluate(b), logic.getTerm_false());
}

TEST_F(UFModelBuilderTest, test_NameCollision) {
    ModelBuilder mb(logic);
    std::string symName("x0");
    SymRef x1_sym = logic.declareFun(symName.c_str(), S, {S});
    mb.addToTheoryFunction(x1_sym, {v0}, v0);
    auto m = mb.build();
    auto templateFun = m->getDefinition(x1_sym);
    std::cout << "testing name collision: the following should be different from `x0`" << std::endl;
    for (PTRef tr : templateFun.getArgs()) {
        std::string argName(logic.getSymName(tr));
        std::cout << argName << std::endl;
        ASSERT_NE(argName, symName);
    }
}

TEST_F(UFModelBuilderTest, test_functionModel) {
    auto model = getModel();
    auto templateFun = model->getDefinition(f_sym);
    std::cout << logic.pp(templateFun.getBody()) << std::endl;
    ASSERT_TRUE(logic.isIte(templateFun.getBody()));
}

class UFConstModelTest : public ::testing::Test {
protected:
    UFConstModelTest() : logic(opensmt::Logic_t::QF_UF), ms(logic, c, "uf-solver") {
        SRef U = logic.declareUninterpretedSort("U");
        fs = logic.declareFun("f", U, {U});
        x = logic.mkVar(U, "x");
        a = logic.mkConst(U, "a");
        f_a = logic.mkUninterpFun(fs, {a});
        eq_x_f_a = logic.mkEq(x, f_a);
        ms.insertFormula(eq_x_f_a);
        ms.check();
        model = ms.getModel();
    }
    PTRef getModelFor(PTRef tr) { return model->evaluate(tr); }
    TemplateFunction getDefinitionFor(SymRef sr) { return model->getDefinition(sr); }
    Logic logic;
    SMTConfig c;
    MainSolver ms;
    std::unique_ptr<Model> model;
    SymRef fs;
    PTRef a;
    PTRef x;
    PTRef f_a;
    PTRef eq_x_f_a;
};

TEST_F(UFConstModelTest, test_constModel) {
    PTRef a_model = getModelFor(a);
    auto a_model_name = logic.pp(a_model);
    ASSERT_EQ(strcmp(a_model_name.c_str(), "a"), 0);
    PTRef f_a_model = getModelFor(f_a);
    PTRef x_model = getModelFor(x);
    ASSERT_EQ(f_a_model, x_model);

    TemplateFunction tf = model->getDefinition(fs);
    Logic::SubstMap sm;
    sm.insert(tf.getArgs()[0], a);
    PTRef rewritten = Substitutor(logic, sm).rewrite(tf.getBody());
    ASSERT_EQ(rewritten, x_model);
}

class LAModelTest : public ::testing::Test {
protected:
    LAModelTest(): logic{opensmt::Logic_t::QF_LRA} {}
    virtual void SetUp() {
        x = logic.mkRealVar("x");
        y = logic.mkRealVar("y");
        z = logic.mkRealVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
    }
    SMTConfig config;
    ArithLogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;

    std::unique_ptr<Model> getModel() {
        Model::Evaluation eval {
                std::make_pair(x, logic.getTerm_RealOne()),
                std::make_pair(y, logic.getTerm_RealZero()),
                std::make_pair(z, logic.getTerm_RealOne()),
                std::make_pair(a, logic.getTerm_true()),
                std::make_pair(b, logic.getTerm_false())
        };
        return std::unique_ptr<Model>(new Model(logic, eval));
    }

};



TEST_F(LAModelTest, test_inputVarValues) {
    auto model = getModel();
    EXPECT_EQ(model->evaluate(x), logic.getTerm_RealOne());
    EXPECT_EQ(model->evaluate(y), logic.getTerm_RealZero());
    EXPECT_EQ(model->evaluate(z), logic.getTerm_RealOne());
    EXPECT_EQ(model->evaluate(a), logic.getTerm_true());
    EXPECT_EQ(model->evaluate(b), logic.getTerm_false());
}

TEST_F(LAModelTest, test_constants) {
    auto model = getModel();
    PTRef tval = logic.getTerm_true();
    PTRef fval = logic.getTerm_false();
    EXPECT_EQ(model->evaluate(fval), fval);
    EXPECT_EQ(model->evaluate(tval), tval);

    PTRef fortytwo = logic.mkRealConst(42);
    EXPECT_EQ(model->evaluate(fortytwo), fortytwo);
    PTRef one = logic.mkRealConst(1);
    EXPECT_EQ(model->evaluate(one), logic.getTerm_RealOne());
    PTRef zero = logic.mkRealConst(FastRational(0));
    EXPECT_EQ(model->evaluate(zero), logic.getTerm_RealZero());
}

TEST_F(LAModelTest, test_derivedBooleanTerms) {
    auto model = getModel();
    PTRef tval = logic.getTerm_true();
    PTRef fval = logic.getTerm_false();

    PTRef and_false = logic.mkAnd(a,b);
    PTRef or_true = logic.mkOr(a,b);
    PTRef not_true = logic.mkNot(b);
    PTRef not_false = logic.mkNot(a);
    EXPECT_EQ(model->evaluate(and_false), fval);
    EXPECT_EQ(model->evaluate(or_true), tval);
    EXPECT_EQ(model->evaluate(not_true), tval);
    EXPECT_EQ(model->evaluate(not_false), fval);
}

TEST_F(LAModelTest, test_derivedArithmeticTerms) {
    auto model = getModel();
    PTRef two = logic.mkRealConst(2);
    PTRef five = logic.mkRealConst(5);
    vec<PTRef> args {x,z};
    EXPECT_EQ(model->evaluate(logic.mkPlus(args)), two);
    EXPECT_EQ(model->evaluate(logic.mkTimes(five, x)), five);
    EXPECT_EQ(model->evaluate(logic.mkTimes(five, y)), logic.getTerm_RealZero());
}

TEST_F(LAModelTest, test_derivedArithmeticAtoms) {
    auto model = getModel();
    PTRef tval = logic.getTerm_true();
    PTRef fval = logic.getTerm_false();

    EXPECT_EQ(model->evaluate(logic.mkLeq(x, y)), fval);
    EXPECT_EQ(model->evaluate(logic.mkLt(x, y)), fval);
    EXPECT_EQ(model->evaluate(logic.mkGeq(x, y)), tval);
    EXPECT_EQ(model->evaluate(logic.mkGt(x, y)), tval);

    EXPECT_EQ(model->evaluate(logic.mkLeq(y, z)), tval);
    EXPECT_EQ(model->evaluate(logic.mkLt(y, z)), tval);
    EXPECT_EQ(model->evaluate(logic.mkGeq(y, z)), fval);
    EXPECT_EQ(model->evaluate(logic.mkGt(y, z)), fval);

    EXPECT_EQ(model->evaluate(logic.mkLeq(x, z)), tval);
    EXPECT_EQ(model->evaluate(logic.mkLt(x, z)), fval);
    EXPECT_EQ(model->evaluate(logic.mkGeq(x, z)), tval);
    EXPECT_EQ(model->evaluate(logic.mkGt(x, z)), fval);

}


class ModelIntegrationTest : public ::testing::Test {
protected:
    ModelIntegrationTest() {}
    std::unique_ptr<Opensmt> getLRAOsmt() {
        return std::unique_ptr<Opensmt>(new Opensmt(opensmt_logic::qf_lra, "test"));
    }

    std::unique_ptr<Opensmt> getUFOsmt() {
        return std::unique_ptr<Opensmt>(new Opensmt(opensmt_logic::qf_uf, "test"));
    }

};

TEST_F(ModelIntegrationTest, testSingleAssert) {
    auto osmt = getLRAOsmt();
    ArithLogic& logic = osmt->getLRALogic();
    PTRef x = logic.mkRealVar("x");
    PTRef y = logic.mkRealVar("y");
    PTRef fla = logic.mkLt(x, y);
    MainSolver& mainSolver = osmt->getMainSolver();
    mainSolver.insertFormula(fla);
    sstat res = mainSolver.check();
    ASSERT_EQ(res, s_True);
    auto model = mainSolver.getModel();
    EXPECT_EQ(model->evaluate(fla), logic.getTerm_true());
}

TEST_F(ModelIntegrationTest, testSubstitutions) {
    auto osmt = getLRAOsmt();
    Logic& logic = osmt->getLogic();
    PTRef x = logic.mkBoolVar("x");
    PTRef y = logic.mkBoolVar("y");
    PTRef fla = logic.mkEq(x, logic.mkNot(y));
    MainSolver& mainSolver = osmt->getMainSolver();
    mainSolver.insertFormula(fla);
    sstat res = mainSolver.check();
    ASSERT_EQ(res, s_True);
//    auto xval = mainSolver.getValue(x);
//    auto yval = mainSolver.getValue(y);
//    std::cout << logic.printTerm(xval.tr) << " : " << xval.val << '\n';
//    std::cout << logic.printTerm(yval.tr) << " : " << yval.val << std::endl;
    auto model = mainSolver.getModel();
    EXPECT_EQ(model->evaluate(fla), logic.getTerm_true());
}

TEST_F(ModelIntegrationTest, testTrivialBooleanSubstitutionNegation) {
    auto osmt = getLRAOsmt();
    Logic& logic = osmt->getLogic();
    PTRef x = logic.mkBoolVar("x");
    PTRef fla = logic.mkNot(x);
    MainSolver& mainSolver = osmt->getMainSolver();
    mainSolver.insertFormula(fla);
    sstat res = mainSolver.check();
    ASSERT_EQ(res, s_True);
    auto model = mainSolver.getModel();
    EXPECT_EQ(model->evaluate(x), logic.getTerm_false());
    EXPECT_EQ(model->evaluate(fla), logic.getTerm_true());
}

TEST_F(ModelIntegrationTest, testIteWithSubstitution) {
    auto osmt = getLRAOsmt();
    ArithLogic& logic = osmt->getLRALogic();
    PTRef x = logic.mkRealVar("x");
    PTRef y = logic.mkRealVar("y");
    PTRef ite = logic.mkIte(logic.mkBoolVar("c"), x, logic.mkPlus(x, logic.getTerm_RealOne()));
    PTRef fla = logic.mkEq(y, ite);
    MainSolver & mainSolver = osmt->getMainSolver();
    mainSolver.insertFormula(fla);
    auto res = mainSolver.check();
    ASSERT_EQ(res, s_True);
    auto model = mainSolver.getModel();
    EXPECT_EQ(model->evaluate(fla), logic.getTerm_true());
}

TEST_F(ModelIntegrationTest, testIteWithSubstitution_SubtermsHaveValue) {
    auto osmt = getLRAOsmt();
    ArithLogic& logic = osmt->getLRALogic();
    PTRef x = logic.mkRealVar("x");
    PTRef y = logic.mkRealVar("y");
    PTRef c = logic.mkBoolVar("c");
    PTRef one = logic.getTerm_RealOne();
    PTRef ite = logic.mkIte(c, x, logic.mkPlus(x, one));
    PTRef eq = logic.mkEq(y, ite);
    PTRef fla = logic.mkAnd({eq, logic.mkLeq(one, y), logic.mkLeq(x, logic.getTerm_RealZero())});
    MainSolver & mainSolver = osmt->getMainSolver();
    mainSolver.insertFormula(fla);
    auto res = mainSolver.check();
    ASSERT_EQ(res, s_True);
    auto model = mainSolver.getModel();
//    std::cout << logic.printTerm(x) << " := " << logic.printTerm(model->evaluate(x)) << '\n';
//    std::cout << logic.printTerm(y) << " := " << logic.printTerm(model->evaluate(y)) << '\n';
//    std::cout << logic.printTerm(c) << " := " << logic.printTerm(model->evaluate(c)) << '\n';
    EXPECT_EQ(model->evaluate(fla), logic.getTerm_true());
    EXPECT_EQ(model->evaluate(c), logic.getTerm_false());
}


