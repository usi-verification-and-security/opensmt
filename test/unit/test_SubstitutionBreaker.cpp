//
// Created by prova on 21.11.19.
//
#include <gtest/gtest.h>
#include <Logic.h>
#include <Map.h>
#include <SubstLoopBreaker.h>

typedef Map<PTRef,PtAsgn,PTRefHash>::Pair spair;

TEST(SubstitutionBreaker, test_getVars) {
    Logic logic;


    char *tmp;
    SRef U = logic.declareSort("U", &tmp);
    PTRef a = logic.mkVar(U, "a");
    PTRef b = logic.mkVar(U, "b");
    PTRef c = logic.mkVar(U, "c");
    SymRef fun = logic.declareFun("f", U, {U, U, U}, &tmp, false);
    PTRef f = logic.mkUninterpFun(fun, {a, b, a});
    PTRef f1 = logic.mkUninterpFun(fun, {f, c, f});

    TargetVarListAllocator tvl(1024);
    SubstNodeAllocator sna(tvl, logic, 1024);
    SNRef snr = sna.alloc(a, f1);
    for (int i = 0; i < sna[snr].nChildren(); i++) {
        char *n = logic.pp(sna[snr].getChildTerm(i));
        cerr << n << " \n";
        free(n);
    }
    ASSERT_EQ(sna[snr].nChildren(), 3);
}

TEST(SubstitutionBreaker, test_Simple) {
    Logic logic;


    PTRef a = logic.mkVar(logic.getSort_bool(), "a");
    Map<PTRef,PtAsgn,PTRefHash> substs;
    substs.insert(a, {logic.getTerm_true(), l_True});

    SubstLoopBreaker slb(logic);

    Map<PTRef,PtAsgn,PTRefHash> subst_map = slb(std::move(substs));
    ASSERT_TRUE(subst_map.has(a));
}

TEST(SubstitutionBreaker, test_getLoops) {
    Logic logic;

    char* tmp;
    SRef U = logic.declareSort("U", &tmp);
    PTRef a = logic.mkVar(U, "a");
    PTRef b = logic.mkVar(U, "b");
    PTRef c = logic.mkVar(U, "c");
    PTRef d = logic.mkVar(U, "d");
    PTRef e = logic.mkVar(U, "e");
    SymRef fun = logic.declareFun("f", U, {U}, &tmp, false);
    PTRef f = logic.mkUninterpFun(fun, {a});

    Map<PTRef,PtAsgn,PTRefHash> substs;
    substs.insert(a, {f, l_True});
    substs.insert(b, {a, l_True});
    substs.insert(c, {b, l_True});
    substs.insert(d, {e, l_True});

    SubstLoopBreaker slb(logic);
    vec<SNRef> startNodes = slb.constructSubstitutionGraph(std::move(substs));
    std::cerr << slb.printGraphAndLoops(startNodes, {}) << std::endl;
    ASSERT_GT(startNodes.size(), 0);
    vec<vec<SNRef>> loops = slb.findLoops(startNodes);
    ASSERT_EQ(loops.size(), 0); // The system does not remove self-loops
    std::cerr << slb.printGraphAndLoops(startNodes, loops) << std::endl;
}

TEST(SubstitutionBreaker, test_getLoops2) {
    Logic logic;

    char* tmp;
    SRef U = logic.declareSort("U", &tmp);
    PTRef a1 = logic.mkVar(U, "a1");
    PTRef b1 = logic.mkVar(U, "b1");
    PTRef c1 = logic.mkVar(U, "c1");
    PTRef a2 = logic.mkVar(U, "a2");
    PTRef b2 = logic.mkVar(U, "b2");
    PTRef c2 = logic.mkVar(U, "c2");
    PTRef start = logic.mkVar(U, "start");
    SymRef symb_f = logic.declareFun("f", U, {U}, &tmp, false);
    SymRef symb_g = logic.declareFun("g", U, {U}, &tmp, false);
    SymRef symb_h = logic.declareFun("g", U, {U, U}, &tmp, false);
    SymRef symb_h2 = logic.declareFun("g", U, {U, U, U}, &tmp, false);

    PTRef f_b1 = logic.mkUninterpFun(symb_f, {b1});
    PTRef h_c1_c2 = logic.mkUninterpFun(symb_h, {c1, c2});
    PTRef f_a1 = logic.mkUninterpFun(symb_f, {a1});
    PTRef g_b2 = logic.mkUninterpFun(symb_g, {b2});
    PTRef g_c2 = logic.mkUninterpFun(symb_g, {c2});
    PTRef h2_a1_b1_a2 = logic.mkUninterpFun(symb_h2, {a1, b1, a2});
    PTRef h_b1_a2 = logic.mkUninterpFun(symb_h, {b1, a2});


    Map<PTRef,PtAsgn,PTRefHash> substs;

    substs.insert(a1, {f_b1, l_True});
    substs.insert(b1, {h_c1_c2, l_True});
    substs.insert(c1, {f_a1, l_True});
    substs.insert(a2, {g_b2, l_True});
    substs.insert(b2, {g_c2, l_True});
    substs.insert(c2, {h2_a1_b1_a2, l_True});
    substs.insert(start, {h_b1_a2, l_True});

    SubstLoopBreaker slb(logic);
    vec<SNRef> startNodes = slb.constructSubstitutionGraph(std::move(substs));
    ASSERT_GT(startNodes.size(), 0);
    vec<vec<SNRef>> loops = slb.findLoops(startNodes);
    ASSERT_EQ(loops.size(), 1);
}

TEST(SubstitutionBreaker, test_getLoops3) {
    Logic logic;

    char* tmp;
    SRef U = logic.declareSort("U", &tmp);
    PTRef e0 = logic.mkVar(U, "e0");
    PTRef e1 = logic.mkVar(U, "e1");
    PTRef e2 = logic.mkVar(U, "e2");
    PTRef e4 = logic.mkVar(U, "e4");

    SymRef symb_op = logic.declareFun("op", U, {U, U}, &tmp, false);

    PTRef op_e2_e1 = logic.mkUninterpFun(symb_op, {e2, e1});
    PTRef op_e2_e2 = logic.mkUninterpFun(symb_op, {e2, e2});
    PTRef op_e0_e0 = logic.mkUninterpFun(symb_op, {e0, e0});
    PTRef op_e4_e1 = logic.mkUninterpFun(symb_op, {e4, e1});

    Map<PTRef,PtAsgn,PTRefHash> substs;

    substs.insert(e0, {op_e2_e1, l_True});
    substs.insert(e4, {op_e2_e2, l_True});
    substs.insert(e1, {op_e0_e0, l_True});
    substs.insert(e2, {op_e4_e1, l_True});

    SubstLoopBreaker slb(logic);
    Map<PTRef,PtAsgn,PTRefHash> new_substs = slb(std::move(substs));

    SubstLoopBreaker slb2(logic);
    vec<SNRef> startNodes = slb2.constructSubstitutionGraph(std::move(new_substs));

    std::cerr << slb2.printGraphAndLoops(startNodes, {}) << std::endl;
    vec<vec<SNRef>> loops = slb2.findLoops(startNodes);
    ASSERT_EQ(loops.size(), 0);
}
