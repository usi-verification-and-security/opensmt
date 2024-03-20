//
// Created by Martin Blicha on 07.07.21.
//

#include <gtest/gtest.h>
#include <PG.h>

TEST(ProofTest, test_mergeClauses_PivotPresent_NoDuplicates) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 2);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
}

TEST(ProofTest, test_mergeClauses_PivotPresent_Duplicates) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false), mkLit(2,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false), mkLit(3,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 3);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
    EXPECT_EQ(res[2], mkLit(3,false));
}

TEST(ProofTest, test_mergeClauses_GarbageInResult) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false) };
    std::vector<Lit> res { mkLit(100, true), mkLit(42, false), mkLit(0, true), mkLit(0, true) };
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 2);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
}

TEST(ProofTest, test_mergeClauses_DuplicateAfterFirstEnd) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false), mkLit(4,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 4);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
    EXPECT_EQ(res[2], mkLit(3,false));
    EXPECT_EQ(res[3], mkLit(4,false));
}

TEST(ProofTest, test_mergeClauses_DuplicateAfterSecondEnd) {
    std::vector<Lit> left { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> right { mkLit(0, true), mkLit(1,false), mkLit(4,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 4);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
    EXPECT_EQ(res[2], mkLit(3,false));
    EXPECT_EQ(res[3], mkLit(4,false));
}

TEST(ProofTest, test_mergeClauses_PivotAfterSecondEnd) {
    std::vector<Lit> left { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> right { mkLit(1, false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 3);
    EXPECT_EQ(res[0], mkLit(2,false));
    EXPECT_EQ(res[1], mkLit(3,false));
    EXPECT_EQ(res[2], mkLit(4,false));
}

TEST(ProofTest, test_mergeClauses_PivotAfterFirstEnd) {
    std::vector<Lit> left { mkLit(1, false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 3);
    EXPECT_EQ(res[0], mkLit(2,false));
    EXPECT_EQ(res[1], mkLit(3,false));
    EXPECT_EQ(res[2], mkLit(4,false));
}

// Reduction algorithms

class ReductionTest : public ::testing::Test {
protected:
    ReductionTest(): logic{opensmt::Logic_t::QF_BOOL}, config{}, theory{config, logic}, partitionManager{logic}, termMapper{logic}, ca{}, proof{ca} {}
    virtual void SetUp() {
        a_term = logic.mkBoolVar("a");
        b_term = logic.mkBoolVar("b");
        c_term = logic.mkBoolVar("c");
        d_term = logic.mkBoolVar("d");
        e_term = logic.mkBoolVar("e");

        a = termMapper.getOrCreateLit(a_term);
        b = termMapper.getOrCreateLit(b_term);
        c = termMapper.getOrCreateLit(c_term);
        d = termMapper.getOrCreateLit(d_term);
        e = termMapper.getOrCreateLit(e_term);

        partitionManager.addIPartitions(a_term, 1);
        partitionManager.addIPartitions(b_term, 1);
        partitionManager.addIPartitions(c_term, 1);
        partitionManager.addIPartitions(d_term, 1);
        partitionManager.addIPartitions(e_term, 1);

    }
    Logic logic;
    SMTConfig config;
    UFTheory theory;
    PartitionManager partitionManager;
    TermMapper termMapper;
    ClauseAllocator ca;
    ResolutionProof proof;

    PTRef a_term;
    PTRef b_term;
    PTRef c_term;
    PTRef d_term;
    PTRef e_term;

    Lit a;
    Lit b;
    Lit c;
    Lit d;
    Lit e;
};
TEST_F(ReductionTest, test_recyclePivots) {
    CRef a_b = ca.alloc(vec<Lit>{a,b});
    CRef nb_c = ca.alloc(vec<Lit>{~b,c});
    CRef nb_nc = ca.alloc(vec<Lit>{~b,~c});
    CRef b_nc = ca.alloc(vec<Lit>{b,~c});
    CRef na_c = ca.alloc(vec<Lit>{~a,c});
    CRef nc_nd = ca.alloc(vec<Lit>{~c,~d});
    CRef nc_d = ca.alloc(vec<Lit>{~c,d});
    CRef na_d = ca.alloc(vec<Lit>{~a,d});
    vec<CRef> clauses = {a_b,nb_c, nb_nc, b_nc, na_c, nc_nd, nc_d, na_d};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }
    // Learnt clauses
    CRef a_c = ca.alloc(vec<Lit>{a,c}, {true, 0});
    CRef nd = ca.alloc(vec<Lit>{~d}, {true, 0});

    proof.beginChain(a_b);
    proof.addResolutionStep(nb_c, var(b));
    proof.endChain(a_c);

    proof.beginChain(nb_nc);
    proof.addResolutionStep(a_c, var(c));
    proof.addResolutionStep(a_b, var(b));
    proof.addResolutionStep(na_c, var(a));
    proof.addResolutionStep(nc_nd, var(c));
    proof.endChain(nd);

    proof.beginChain(nc_d);
    proof.addResolutionStep(a_c, var(c));
    proof.addResolutionStep(na_d,var(a));
    proof.addResolutionStep(nd, var(d));
    proof.endChain(CRef_Undef);

    ProofGraph pg(config, theory.getLogic(), termMapper, proof);
    pg.fillProofGraph();
    pg.checkProof(true);
//    pg.printProofAsDotty(std::cout);
    pg.recyclePivotsIter();
    pg.checkProof(true);
//    std::cout << "\n\n\n";
//    pg.printProofAsDotty(std::cout);
    pg.emptyProofGraph();
    EXPECT_TRUE(true);
}

TEST_F(ReductionTest, test_recyclePivots_IdenticalAntecedents) {
    CRef a_d = ca.alloc(vec<Lit>{a,d});
    CRef b_nd = ca.alloc(vec<Lit>{b,~d});
    CRef na_c = ca.alloc(vec<Lit>{~a,c});
    CRef na_nc = ca.alloc(vec<Lit>{~a,~c});
    CRef nb_nd = ca.alloc(vec<Lit>{~b,~d});
    CRef d_e = ca.alloc(vec<Lit>{d,e});
    CRef b_nc_nd_ne = ca.alloc(vec<Lit>{b,~c,~d,~e});
    CRef d_ne = ca.alloc(vec<Lit>{d,~e});
    CRef nb_ne = ca.alloc(vec<Lit>{~b,~e});
    vec<CRef> clauses = {a_d, b_nd, na_c, na_nc, nb_nd, d_e, b_nc_nd_ne, d_ne, nb_ne};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }
    // Learnt clauses
    CRef a_b = ca.alloc(vec<Lit>{a,b}, {true, 0});

    proof.beginChain(a_d);
    proof.addResolutionStep(b_nd, var(d));
    proof.endChain(a_b);

    CRef b_c = ca.alloc(vec<Lit>{b,c}, {true, 0});

    proof.beginChain(na_c);
    proof.addResolutionStep(a_b, var(a));
    proof.endChain(b_c);

    CRef ne = ca.alloc(vec<Lit>{~e}, {true, 0});

    proof.beginChain(b_nc_nd_ne);
    proof.addResolutionStep(b_c, var(c));
    proof.addResolutionStep(nb_ne, var(b));
    proof.addResolutionStep(d_ne, var(d));
    proof.endChain(ne);

    // bot
    proof.beginChain(na_nc);
    proof.addResolutionStep(b_c, var(c));
    proof.addResolutionStep(a_b,var(a));
    proof.addResolutionStep(nb_nd, var(b));
    proof.addResolutionStep(d_e, var(d));
    proof.addResolutionStep(ne, var(e));
    proof.endChain(CRef_Undef);

    ProofGraph pg(config, theory.getLogic(), termMapper, proof);
    pg.fillProofGraph();
    pg.checkProof(true);
//    pg.printProofAsDotty(std::cout);
    pg.recyclePivotsIter();
    pg.checkProof(true);
//    std::cout << "\n\n\n";
//    pg.printProofAsDotty(std::cout);
    pg.emptyProofGraph();
    EXPECT_TRUE(true);
}

TEST_F(ReductionTest, test_recyclePivots_IdenticalAntecedents_AfterPhaseOneReplace) {
    CRef a_d = ca.alloc(vec<Lit>{a,d});
    CRef b_nd = ca.alloc(vec<Lit>{b,~d});
    CRef na_c = ca.alloc(vec<Lit>{~a,c});
    CRef na_nc = ca.alloc(vec<Lit>{~a,~c});
    CRef nb_c_nd = ca.alloc(vec<Lit>{~b,c,~d});
    CRef nc_nd = ca.alloc(vec<Lit>{~c,~d});
    CRef d_e = ca.alloc(vec<Lit>{d,e});
    CRef b_nc_nd_ne = ca.alloc(vec<Lit>{b,~c,~d,~e});
    CRef d_ne = ca.alloc(vec<Lit>{d,~e});
    CRef nb_ne = ca.alloc(vec<Lit>{~b,~e});
    vec<CRef> clauses = {a_d, b_nd, na_c, na_nc, nb_c_nd, nc_nd, d_e, b_nc_nd_ne, d_ne, nb_ne};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }
    // Learnt clauses
    CRef a_b = ca.alloc(vec<Lit>{a,b}, {true, 0});

    proof.beginChain(a_d);
    proof.addResolutionStep(b_nd, var(d));
    proof.endChain(a_b);

    CRef b_c = ca.alloc(vec<Lit>{b,c}, {true, 0});

    proof.beginChain(na_c);
    proof.addResolutionStep(a_b, var(a));
    proof.endChain(b_c);

    CRef ne = ca.alloc(vec<Lit>{~e}, {true, 0});

    proof.beginChain(b_nc_nd_ne);
    proof.addResolutionStep(b_c, var(c));
    proof.addResolutionStep(nb_ne, var(b));
    proof.addResolutionStep(d_ne, var(d));
    proof.endChain(ne);

    // bot
    proof.beginChain(na_nc);
    proof.addResolutionStep(b_c, var(c));
    proof.addResolutionStep(a_b,var(a));
    proof.addResolutionStep(nb_c_nd, var(b));
    proof.addResolutionStep(nc_nd, var(c));
    proof.addResolutionStep(d_e, var(d));
    proof.addResolutionStep(ne, var(e));
    proof.endChain(CRef_Undef);

    ProofGraph pg(config, theory.getLogic(), termMapper, proof);
    pg.fillProofGraph();
    pg.checkProof(true);
//    pg.printProofAsDotty(std::cout);
    pg.recyclePivotsIter();
    pg.checkProof(true);
//    std::cout << "\n\n\n";
//    pg.printProofAsDotty(std::cout);
    pg.emptyProofGraph();
    EXPECT_TRUE(true);
}

TEST_F(ReductionTest, test_proofTransformAndRestructure) {
    CRef a_b = ca.alloc(vec<Lit>{a,b});
    CRef na_c = ca.alloc(vec<Lit>{~a,c});
    CRef na_nb_d = ca.alloc(vec<Lit>{~a,~b,d});
    CRef a_e = ca.alloc(vec<Lit>{a,e});
    CRef d_ne = ca.alloc(vec<Lit>{d,~e});
    CRef nc_d = ca.alloc(vec<Lit>{~c,d});
    CRef nd = ca.alloc(vec<Lit>{~d});
    vec<CRef> clauses = {a_b, na_c, na_nb_d, a_e, d_ne, nc_d, nd};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }
    // Learnt clauses
    CRef a_d = ca.alloc(vec<Lit>{a,d}, {true, 0});

    proof.beginChain(a_e);
    proof.addResolutionStep(d_ne, var(e));
    proof.endChain(a_d);

    // bot
    proof.beginChain(a_b);
    proof.addResolutionStep(na_c, var(a));
    proof.addResolutionStep(na_nb_d,var(b));
    proof.addResolutionStep(a_d, var(a));
    proof.addResolutionStep(nc_d, var(c));
    proof.addResolutionStep(nd, var(d));
    proof.endChain(CRef_Undef);

    ProofGraph pg(config, theory.getLogic(), termMapper, proof);
    pg.fillProofGraph();
    pg.checkProof(true);
//    pg.printProofAsDotty(std::cout);
    pg.proofTransformAndRestructure(-1,1,true, [&pg](RuleContext & ra1, RuleContext & ra2) {
        return pg.handleRuleApplicationForReduction(ra1, ra2);
    });
    pg.checkProof(true);
//    std::cout << "\n\n\n";
//    pg.printProofAsDotty(std::cout);
    pg.emptyProofGraph();
    EXPECT_TRUE(true);
}


/*
 * This proof shows a situation where a node can end up with identical antecedents in the algorithm
 * ProofGraph::proofTransformAndRestructure with ProofGraph::handleRuleApplicationForReduction
 * as the rule selection method.
 *
 * The smallest example of that (shown in this test) is a diamond-like subproof
 *  ~ab        a v C        ~a~b
 *       b v C        ~b v C
 *              C
 *  If the literal 'a' in "a v C" turns out to be unnecessary (because of redundancies above it) then
 *  the algorithm runs into the situation when two antecedents of a node is the same node.
 *  However, the situation is not problematic and such node should just be replaced with its single parent.
 *
 */
TEST_F(ReductionTest, test_proofTransformAndRestructure_IdenticalAntecedents) {
    CRef a_b = ca.alloc(vec<Lit>{a,b});
    CRef na_c = ca.alloc(vec<Lit>{~a,c});
    CRef na_nb_d = ca.alloc(vec<Lit>{~a,~b,d});
    CRef nd_e = ca.alloc(vec<Lit>{~d,e});
    CRef nd_ne = ca.alloc(vec<Lit>{~d,~e});
    CRef nc = ca.alloc(vec<Lit>{~c});
    CRef aa = ca.alloc(vec<Lit>{a});

    vec<CRef> clauses = {a_b, na_c, na_nb_d, nd_e, nd_ne, nc, aa};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }

    // learnt clauses
    CRef na_c_d = ca.alloc(vec<Lit>{~a,c,d}, {true, 0});
    proof.beginChain(a_b);
    proof.addResolutionStep(na_c, var(a));
    proof.addResolutionStep(na_nb_d,var(b));
    proof.endChain(na_c_d);

    CRef na_c_e = ca.alloc(vec<Lit>{~a,c,e}, {true, 0});
    proof.beginChain(nd_e);
    proof.addResolutionStep(na_c_d, var(d));
    proof.endChain(na_c_e);

    // bot
    proof.beginChain(nd_ne);
    proof.addResolutionStep(na_c_d, var(d));
    proof.addResolutionStep(na_c_e, var(e));
    proof.addResolutionStep(aa, var(a));
    proof.addResolutionStep(nc, var(c));
    proof.endChain(CRef_Undef);

    ProofGraph pg(config, theory.getLogic(), termMapper, proof);
    pg.fillProofGraph();
    pg.checkProof(true);
//    pg.printProofAsDotty(std::cout);
    pg.proofTransformAndRestructure(-1,1,true, [&pg](RuleContext & ra1, RuleContext & ra2) {
        return pg.handleRuleApplicationForReduction(ra1, ra2);
    });
    pg.checkProof(true);
//    std::cout << "\n\n\n";
//    pg.printProofAsDotty(std::cout);
    pg.emptyProofGraph();
    EXPECT_TRUE(true);
}
