//
// Created by prova on 21.11.19.
//
#include <gtest/gtest.h>
#include <Logic.h>
#include <SMTConfig.h>
#include <Map.h>
#include <SubstLoopBreaker.h>

TEST(SubstitutionBreaker, test_getVars) {
    SMTConfig config;
    Logic logic{config};


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

TEST(SubstitutionBreaker, test_getLoops) {
    SMTConfig config;
    Logic logic{config};

    char* tmp;
    SRef U = logic.declareSort("U", &tmp);
    PTRef a = logic.mkVar(U, "a");
    PTRef b = logic.mkVar(U, "b");
    PTRef c = logic.mkVar(U, "c");
    PTRef d = logic.mkVar(U, "d");
    PTRef e = logic.mkVar(U, "e");
    SymRef fun = logic.declareFun("f", U, {U}, &tmp, false);
    SymRef fun2 = logic.declareFun("g", U, {U, U, U}, &tmp, false);
    PTRef f = logic.mkUninterpFun(fun, {a});
    PTRef g = logic.mkUninterpFun(fun2, {c, d, e});
    typedef Map<PTRef,PtAsgn,PTRefHash>::Pair spair;
    vec<spair*> substs;
    spair p1 = spair{a, {f, l_True}};
    spair p2 = spair{b, {a, l_True}};
    spair p3 = spair{c, {b, l_True}};
    spair p4 = spair{d, {e, l_True}};

    substs.push(&p1);
    substs.push(&p2);
    substs.push(&p3);
    substs.push(&p4);


    SubstLoopBreaker slb(logic);
    vec<SNRef> startNodes = slb.constructSubstitutionGraph(std::move(substs));
    std::cerr << slb.printGraphAndLoops(startNodes, {}).str() << std::endl;
    ASSERT_TRUE(startNodes.size() > 0);
    vec<vec<SNRef>> loops = slb.findLoops(startNodes);
    std::cerr << slb.printGraphAndLoops(startNodes, loops).str() << std::endl;
    slb.breakLoops(loops);
    std::cerr << slb.printGraphAndLoops(startNodes, loops).str() << std::endl;
//    ASSERT_TRUE(substs[a].sgn == l_False || substs[b].sgn == l_False);
}

TEST(SubstitutionBreaker, test_getLoops2) {
    SMTConfig config;
    Logic logic{config};

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

    typedef Map<PTRef,PtAsgn,PTRefHash>::Pair spair;

    vec<spair*> substs;

    spair p_a1     {a1, {f_b1, l_True}};
    spair p_b1     {b1, {h_c1_c2, l_True}};
    spair p_c1     {c1, {f_a1, l_True}};
    spair p_a2     {a2, {g_b2, l_True}};
    spair p_b2     {b2, {g_c2, l_True}};
    spair p_c2     {c2, {h2_a1_b1_a2, l_True}};
    spair p_start  {start, {h_b1_a2, l_True}};

    substs.push(&p_a1);
    substs.push(&p_b1);
    substs.push(&p_c1);
    substs.push(&p_a2);
    substs.push(&p_b2);
    substs.push(&p_c2);
    substs.push(&p_start);

    SubstLoopBreaker slb(logic);
    vec<SNRef> startNodes = slb.constructSubstitutionGraph(std::move(substs));
    std::cerr << slb.printGraphAndLoops(startNodes, {}).str() << std::endl;
    ASSERT_TRUE(startNodes.size() > 0);
    vec<vec<SNRef>> loops = slb.findLoops(startNodes);
    std::cerr << slb.printGraphAndLoops(startNodes, loops).str() << std::endl;
    slb.breakLoops(loops);
//    std::cerr << slb.printGraphAndLoops(startNodes, loops).str() << std::endl;
//    ASSERT_TRUE(substs[a].sgn == l_False || substs[b].sgn == l_False);
}

TEST(SubstitutionBreaker, test_getLoops3) {
    SMTConfig config;
    Logic logic{config};

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

    typedef Map<PTRef,PtAsgn,PTRefHash>::Pair spair;

    vec<spair*> substs;

    spair p_e0     {e0, {op_e2_e1, l_True}};
    spair p_e4     {e4, {op_e2_e2, l_True}};
    spair p_e1     {e1, {op_e0_e0, l_True}};
    spair p_e2     {e2, {op_e4_e1, l_True}};

    substs.push(&p_e0);
    substs.push(&p_e4);
    substs.push(&p_e1);
    substs.push(&p_e2);

    SubstLoopBreaker slb(logic);
    Map<PTRef,PtAsgn,PTRefHash> new_substs = slb(std::move(substs));

    SubstLoopBreaker slb2(logic);
    vec<SNRef> startNodes = slb2.constructSubstitutionGraph(std::move(new_substs.getKeysAndValsPtrs()));
    std::cerr << slb2.printGraphAndLoops(startNodes, {}).str() << std::endl;
    vec<vec<SNRef>> loops = slb2.findLoops(startNodes);
    std::cerr << slb2.printGraphAndLoops(startNodes, loops).str() << std::endl;
    vec<SNRef> orphans = slb2.breakLoops(loops);
    for (int i = 0; i < orphans.size(); i++) {
        startNodes.push(orphans[i]);
    }
    sort(startNodes);
    uniq(startNodes);

    std::cerr << slb2.printGraphAndLoops(startNodes, {}).str() << std::endl;
//    std::cerr << slb.printGraphAndLoops(startNodes, loops).str() << std::endl;
//    ASSERT_TRUE(substs[a].sgn == l_False || substs[b].sgn == l_False);
}
