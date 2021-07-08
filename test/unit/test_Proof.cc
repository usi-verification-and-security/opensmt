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
TEST(ProofTest, test_recyclePivots) {
    SMTConfig config;
    Logic logic;
    UFTheory theory(config, logic);
    // Terms
    PTRef a_term = logic.mkBoolVar("a");
    PTRef b_term = logic.mkBoolVar("b");
    PTRef c_term = logic.mkBoolVar("c");
    PTRef d_term = logic.mkBoolVar("d");
    PartitionManager partitionManager(logic);
    partitionManager.addIPartitions(a_term, 1);
    partitionManager.addIPartitions(b_term, 1);
    partitionManager.addIPartitions(c_term, 1);
    partitionManager.addIPartitions(d_term, 1);
    TermMapper termMapper(logic);
    Lit a = termMapper.getOrCreateLit(a_term);
    Lit b = termMapper.getOrCreateLit(b_term);
    Lit c = termMapper.getOrCreateLit(c_term);
    Lit d = termMapper.getOrCreateLit(d_term);
    ClauseAllocator ca;
    CRef a_b = ca.alloc(vec<Lit>{a,b}, false);
    CRef nb_c = ca.alloc(vec<Lit>{~b,c}, false);
    CRef nb_nc = ca.alloc(vec<Lit>{~b,~c}, false);
    CRef b_nc = ca.alloc(vec<Lit>{b,~c}, false);
    CRef na_c = ca.alloc(vec<Lit>{~a,c}, false);
    CRef nc_nd = ca.alloc(vec<Lit>{~c,~d}, false);
    CRef nc_d = ca.alloc(vec<Lit>{~c,d}, false);
    CRef na_d = ca.alloc(vec<Lit>{~a,d}, false);
    vec<CRef> clauses = {a_b,nb_c, nb_nc, b_nc, na_c, nc_nd, nc_d, na_d};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    Proof proof(ca);
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }
    // Learnt clauses
    CRef a_c = ca.alloc(vec<Lit>{a,c}, true);
    CRef nd = ca.alloc(vec<Lit>{~d}, true);

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

    int nVars = 4;
    ProofGraph pg(config, theory, termMapper, proof, partitionManager, nVars);
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

TEST(ProofTest, test_recyclePivots_IdenticalParents) {
    SMTConfig config;
    Logic logic;
    UFTheory theory(config, logic);
    // Terms
    PTRef a_term = logic.mkBoolVar("a");
    PTRef b_term = logic.mkBoolVar("b");
    PTRef c_term = logic.mkBoolVar("c");
    PTRef d_term = logic.mkBoolVar("d");
    PTRef e_term = logic.mkBoolVar("e");
    PartitionManager partitionManager(logic);
    partitionManager.addIPartitions(a_term, 1);
    partitionManager.addIPartitions(b_term, 1);
    partitionManager.addIPartitions(c_term, 1);
    partitionManager.addIPartitions(d_term, 1);
    partitionManager.addIPartitions(e_term, 1);
    TermMapper termMapper(logic);
    Lit a = termMapper.getOrCreateLit(a_term);
    Lit b = termMapper.getOrCreateLit(b_term);
    Lit c = termMapper.getOrCreateLit(c_term);
    Lit d = termMapper.getOrCreateLit(d_term);
    Lit e = termMapper.getOrCreateLit(e_term);
    ClauseAllocator ca;
    CRef a_d = ca.alloc(vec<Lit>{a,d}, false);
    CRef b_nd = ca.alloc(vec<Lit>{b,~d}, false);
    CRef na_c = ca.alloc(vec<Lit>{~a,c}, false);
    CRef na_nc = ca.alloc(vec<Lit>{~a,~c}, false);
    CRef nb_nd = ca.alloc(vec<Lit>{~b,~d}, false);
    CRef d_e = ca.alloc(vec<Lit>{d,e}, false);
    CRef b_nc_nd_ne = ca.alloc(vec<Lit>{b,~c,~d,~e}, false);
    CRef d_ne = ca.alloc(vec<Lit>{d,~e}, false);
    CRef nb_ne = ca.alloc(vec<Lit>{~b,~e}, false);
    vec<CRef> clauses = {a_d, b_nd, na_c, na_nc, nb_nd, d_e, b_nc_nd_ne, d_ne, nb_ne};
    for (CRef cr : clauses) {
        partitionManager.addClauseClassMask(cr, 1);
    }
    Proof proof(ca);
    for (CRef cr : clauses) {
        proof.newOriginalClause(cr);
    }
    // Learnt clauses
    CRef a_b = ca.alloc(vec<Lit>{a,b}, true);

    proof.beginChain(a_d);
    proof.addResolutionStep(b_nd, var(d));
    proof.endChain(a_b);

    CRef b_c = ca.alloc(vec<Lit>{b,c}, true);

    proof.beginChain(na_c);
    proof.addResolutionStep(a_b, var(a));
    proof.endChain(b_c);

    CRef ne = ca.alloc(vec<Lit>{~e}, true);

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

    int nVars = 5;
    ProofGraph pg(config, theory, termMapper, proof, partitionManager, nVars);
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
