/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "InterpolationContext.h"

#include "PG.h"
#include "VerificationUtils.h"
#include "BoolRewriting.h"

class SingleInterpolationComputationContext {
    // Interpolation data for resolution proof element
    struct InterpolationNodeData {
        // NOTE labeling rules for AB variables
        // color a:  bit 1, bit 0
        // color b:  bit 0, bit 1
        // color ab: bit 1, bit 1
        // missing:  bit 0, bit 0
        // This notation is consistent with coloring of inner nodes given by | of antecedents colorings
        ipartitions_t AB_vars_a_colored;
        ipartitions_t AB_vars_b_colored;

        PTRef partialInterpolant;

        InterpolationNodeData() : AB_vars_a_colored(0), AB_vars_b_colored(0), partialInterpolant(PTRef_Undef) {}

        inline void clearSharedVar(int varIndex) {
            clrbit(AB_vars_a_colored, varIndex);
            clrbit(AB_vars_b_colored, varIndex);
        }

        inline void resetLabeling() {
            AB_vars_a_colored = 0;
            AB_vars_b_colored = 0;
        }

        inline bool isColoredA(int i) const {
            return ((tstbit(AB_vars_a_colored, i) == 1) && (tstbit(AB_vars_b_colored, i) == 0));
        }

        inline bool isColoredB(int i) const {
            return ((tstbit(AB_vars_a_colored, i) == 0) && (tstbit(AB_vars_b_colored, i) == 1));
        }

        inline bool isColoredAB(int i) const {
            return ((tstbit(AB_vars_a_colored, i) == 1) && (tstbit(AB_vars_b_colored, i) == 1));
        }

        inline void colorA(int i) {
            setbit(AB_vars_a_colored, i);
            clrbit(AB_vars_b_colored, i);
        }

        inline void colorB(int i) {
            setbit(AB_vars_b_colored, i);
            clrbit(AB_vars_a_colored, i);
        }

        inline void colorAB(int i) {
            setbit(AB_vars_a_colored, i);
            setbit(AB_vars_b_colored, i);
        }
    };

    // NOTE class A has value -1, class B value -2, undetermined value -3, class AB has index bit from 0 onwards
    std::vector<int> AB_vars_mapping;             // Variables of class AB mapping to mpz integer bit index
    std::vector<InterpolationNodeData> nodeData;
    Logic & logic;
    SMTConfig const & config;
    PartitionManager & pmanager;
    ProofGraph const & proofGraph;
    std::unique_ptr<THandler> thandler;
    ipartitions_t const & A_mask;

public:
    int getSharedVarIndex(Var v) const {
        assert(AB_vars_mapping[v] >= 0);
        return AB_vars_mapping[v];
    }

    icolor_t getVarClassFromCache(Var v) const {
        assert((unsigned) v < AB_vars_mapping.size());
        assert(AB_vars_mapping[v] >= -2);
        int c = AB_vars_mapping[v];
        return c == -1 ? icolor_t::I_A : (c == -2 ? icolor_t::I_B : icolor_t::I_AB);
    }

    SingleInterpolationComputationContext(
            SMTConfig const & config,
            Theory & theory,
            TermMapper & termMapper,
            PartitionManager & pmanager,
            ProofGraph const & proof,
            ipartitions_t const & A_mask
    );

    inline bool isColoredA(ProofNode const & n, Var v) const { return nodeData[n.getId()].isColoredA(getSharedVarIndex(v)); }

    inline bool isColoredB(ProofNode const & n, Var v) const { return nodeData[n.getId()].isColoredB(getSharedVarIndex(v)); }

    inline bool isColoredAB(ProofNode const & n, Var v) const { return nodeData[n.getId()].isColoredAB(getSharedVarIndex(v)); }

    inline void colorA(ProofNode & n, Var v) { nodeData[n.getId()].colorA(getSharedVarIndex(v)); }

    inline void colorB(ProofNode & n, Var v) { nodeData[n.getId()].colorB(getSharedVarIndex(v)); }

    inline void colorAB(ProofNode & n, Var v) { nodeData[n.getId()].colorAB(getSharedVarIndex(v)); }

    inline void resetLabeling(ProofNode const & n) { nodeData[n.getId()].resetLabeling(); }

    inline PTRef getPartialInterpolant(ProofNode const & n) { return nodeData[n.getId()].partialInterpolant; }

    inline void setPartialInterpolant(ProofNode const & n, PTRef itp) { nodeData[n.getId()].partialInterpolant = itp; }

    inline void updateColoringfromAnts(ProofNode const & n) {
        assert(not n.isLeaf());
        auto & data = nodeData[n.getId()];
        auto const & ant1Data = nodeData[n.getAnt1()->getId()];
        auto const & ant2Data = nodeData[n.getAnt2()->getId()];
        orbit(data.AB_vars_a_colored, ant1Data.AB_vars_a_colored, ant2Data.AB_vars_a_colored);
        orbit(data.AB_vars_b_colored, ant1Data.AB_vars_b_colored, ant2Data.AB_vars_b_colored);
    }

    inline void clearPivotColoring(ProofNode const & n) {
        assert(not n.isLeaf());
        auto & data = nodeData[n.getId()];
        data.clearSharedVar(getSharedVarIndex(n.getPivot()));
    }

    void initTSolver();
    void backtrackTSolver();
    bool assertLiteralsToTSolver(vec<Lit> const &);

    ipartitions_t const & getVarPartition(Var v) const { return pmanager.getIPartitions(varToPTRef(v)); }
    inline Lit PTRefToLit(PTRef ref) const {return thandler->getTMap().getLit(ref);}
    inline Var PTRefToVar(PTRef ref) const { return thandler->getTMap().getVar(ref); }
    inline PTRef varToPTRef(Var v) const { return thandler->getTMap().varToPTRef(v); }

    icolor_t getSharedVarColorInNode(Var v, ProofNode const & node) const {
        if (isColoredA(node, v)) return icolor_t::I_A;
        else if (isColoredB(node, v)) return icolor_t::I_B;
        else if (isColoredAB(node, v)) return icolor_t::I_AB;

        throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(node.getId()));
    }

    void labelLeaf(ProofNode & n, std::map<Var, icolor_t> const * PSFunction = nullptr);
    template<typename TFun>
    void setLeafLabeling(ProofNode & node, TFun colorABVar);

    void setLeafMcMillanLabeling(ProofNode &);

    void setLeafPudlakLabeling(ProofNode &);

    void setLeafMcMillanPrimeLabeling(ProofNode &);

    void setLeafPSLabeling(ProofNode &, std::map<Var, icolor_t> const & PSFunction);

    void setLeafPSWLabeling(ProofNode &, std::map<Var, icolor_t> const & PSFunction);

    void setLeafPSSLabeling(ProofNode &, std::map<Var, icolor_t> const & PSFunction);

    PTRef getInterpolantForOriginalClause(ProofNode const & node, icolor_t clauseClass) const;
    std::vector<Lit> getRestrictedNodeClause(ProofNode const & node, icolor_t wantedVarClass) const;

    icolor_t getVarClass(Var) const;

    icolor_t getClauseColor(CRef clause) const;

    std::unique_ptr<std::map<Var, icolor_t>> computePSFunction() const;


    PTRef computePartialInterpolantForOriginalClause(ProofNode const & n) const;

    PTRef computePartialInterpolantForTheoryClause(ProofNode const & n);

    PTRef computePartialInterpolantForSplitClause(ProofNode const & n) const;

    PTRef compInterpLabelingInner(ProofNode &);

    icolor_t getPivotColor(ProofNode const &);

    icolor_t getVarColor(ProofNode const & n, Var v) const;

    PTRef produceSingleInterpolant();

    void checkInterAlgo() const;

    bool usingMcMillanInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_mcmillan; }

    bool usingPudlakInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_pudlak; }

    bool usingMcMillanPrimeInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_mcmillanp; }

    bool usingPSInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_ps; }

    bool usingPSWInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_psw; }

    bool usingPSSInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_pss; }

    int verbose() const { return config.verbosity(); }

    bool usingAlternativeInterpolant() const { return (config.proof_alternative_inter() == 1); }

    bool enabledInterpVerif() const { return (config.certify_inter() >= 1); }

    bool enabledPedInterpVerif() const { return (config.certify_inter() >= 2); }

    bool needProofStatistics() const {
        ItpAlgorithm ia = config.getBooleanInterpolationAlgorithm();
        return ((ia == itp_alg_ps) or (ia == itp_alg_psw) or (ia == itp_alg_pss));
    }

    bool verifyPartialInterpolant(ProofNode const &);

    bool verifyPartialInterpolantA(ProofNode const &);

    bool verifyPartialInterpolantB(ProofNode const &);
};

/**************** HELPER METHODS ************************/

namespace {
bool decideOnAlternativeInterpolation(PTRef I1, PTRef I2, Logic const & logic) {
    assert(I1 != PTRef_Undef);
    assert(I2 != PTRef_Undef);
    bool I1_is_true = (I1 == logic.getTerm_true());
    bool I2_is_true = (I2 == logic.getTerm_true());
    bool I1_is_false = (I1 == logic.getTerm_false());
    bool I2_is_false = (I2 == logic.getTerm_false());
    bool I1_is_none = (not I1_is_true and not I1_is_false);
    bool I2_is_none = (not I2_is_true and not I2_is_false);

    // For some combinations of I1, I2, the alternative interpolant
    // has a smaller size!
    // Standard     (I1 \/ p ) /\ (I2 \/ ~p)
    // Alternative  (I1 /\ ~p) \/ (I2 /\ p)

    if (I1_is_false and I2_is_none) return true;
    if (I1_is_none and I2_is_false) return true;
    if (I1_is_false and I2_is_false) return true;
    return false;
}

icolor_t getClass(ipartitions_t const & mask, ipartitions_t const & A_mask) {
    ipartitions_t B_mask = ~A_mask;

    // Check if belongs to A or B
    const bool in_A = ((mask & A_mask) != 0);
    const bool in_B = ((mask & B_mask) != 0);
    assert(in_A or in_B);

    icolor_t clause_color = icolor_t::I_UNDEF;
    if (in_A and not in_B) clause_color = icolor_t::I_A;
    else if (not in_A and in_B) clause_color = icolor_t::I_B;
    else if (in_A and in_B) clause_color = icolor_t::I_AB;
    else throw OsmtInternalException("No class could have been determined");

    return clause_color;
}
}

icolor_t SingleInterpolationComputationContext::getVarColor(ProofNode const & n, Var v) const {
    assert(n.isLeaf());
    // In labeling, classes and colors are distinct
    icolor_t var_class = getVarClass(v);
    assert(var_class == icolor_t::I_A or var_class == icolor_t::I_B or var_class == icolor_t::I_AB);
    icolor_t var_color = var_class == icolor_t::I_B || var_class == icolor_t::I_A ? var_class
                                                                                  : getSharedVarColorInNode(v, n);
    return var_color;
}

// Input: node, current interpolant partition masks for A and B
// Output: returns node pivot color as a, b or ab
// depending on the colors in the node antecedents
icolor_t SingleInterpolationComputationContext::getPivotColor(ProofNode const & n) {
    assert(not n.isLeaf());
    Var v = n.getPivot();
    // In labeling, classes and colors are distinct
    icolor_t var_class = getVarClassFromCache(v);
    if (var_class != icolor_t::I_A and var_class != icolor_t::I_B and var_class != icolor_t::I_AB) {
        throw OsmtInternalException("Pivot " + std::to_string(v) + " has no class");
    }

    // Update AB vars color vectors from antecedents
    updateColoringfromAnts(n);

    // Determine if variable A-local, B-local or AB-common
    icolor_t var_color = var_class;
    if (var_color != icolor_t::I_A and var_color != icolor_t::I_B) {
        assert(var_class == icolor_t::I_AB);
        var_color = getSharedVarColorInNode(v, n);
        // Remove pivot from resolvent if class AB
        clearPivotColoring(n);
    }
    if (proofGraph.isAssumedVar(v)) { // Small hack to deal with assumption literals in proof
        return icolor_t::I_S;
    }
    return var_color;
}

// Input: variable, current interpolant partition masks for A
// Output: returns A-local , B-local or AB-common
icolor_t SingleInterpolationComputationContext::getVarClass(Var v) const {
    if (proofGraph.isAssumedVar(v)) { return icolor_t::I_AB; } // MB: Does not matter for assumed literals
    const ipartitions_t & var_mask = getVarPartition(v);
    return getClass(var_mask, A_mask);
}

// Input: proof node, current interpolant partition masks for A
// Output: returns A, B or AB
icolor_t SingleInterpolationComputationContext::getClauseColor(CRef clause) const {
    auto const & clause_mask = pmanager.getClauseClassMask(clause);
    return getClass(clause_mask, A_mask);
}

std::unique_ptr<std::map<Var, icolor_t>> SingleInterpolationComputationContext::computePSFunction() const {

    auto labels = std::make_unique<std::map<Var, icolor_t>>();

    std::map<Var, int> occ_a, occ_b;

    for (auto leafId : proofGraph.getLeaves()) {
        ProofNode * n = proofGraph.getNode(leafId);
        assert(n and n->isLeaf());
        if (n->getType() != clause_type::CLA_ORIG) {
            continue;
        }
        icolor_t col = getClauseColor(n->getClauseRef());
        for (Lit l : n->getClause()) {
            Var v = var(l);
            icolor_t vclass = getVarClassFromCache(v);
            if (vclass != icolor_t::I_AB) continue;
            if (col == icolor_t::I_A) {
                ++occ_a[v];
                if (occ_b.find(v) == occ_b.end()) {
                    occ_b[v] = 0;
                }
            } else if (col == icolor_t::I_B) {
                ++occ_b[v];
                if (occ_a.find(v) == occ_a.end())
                    occ_a[v] = 0;
            }
        }
    }
    assert(occ_a.size() == occ_b.size());
    for (auto const & entry : occ_a) {
        Var v = entry.first;
        int qtta = entry.second;
        int qttb = occ_b.find(v)->second;
        labels->insert({v, qtta > qttb ? icolor_t::I_A : icolor_t::I_B});
    }
    return labels;
}

void SingleInterpolationComputationContext::checkInterAlgo() const {
    if ( ! ( usingMcMillanInterpolation()
             || usingPudlakInterpolation()
             || usingMcMillanPrimeInterpolation()
             || usingPSInterpolation()
             || usingPSWInterpolation()
             || usingPSSInterpolation()))
        throw OsmtApiException("Please choose 0/1/2/3/4/5 as values for itp_bool_algo");

    if ( verbose() > 0 )
    {
        std::cerr << "# Using ";

        if ( usingPudlakInterpolation() )
            std::cerr << "Pudlak";
        else if ( usingMcMillanInterpolation() )
            std::cerr << "McMillan";
        else if ( usingMcMillanPrimeInterpolation() )
            std::cerr << "McMillan'";
        else if (  usingPSInterpolation() )
            std::cerr << "Proof-Sensitive";
        else if (  usingPSWInterpolation() )
            std::cerr << "Weak Proof-Sensitive";
        else if (  usingPSSInterpolation() )
            std::cerr << "Strong Proof-Sensitive";

        std::cerr << " for propositional interpolation" << '\n';
    }
}

void SingleInterpolationComputationContext::backtrackTSolver() {
    thandler->backtrack(-1);
}

bool SingleInterpolationComputationContext::assertLiteralsToTSolver(vec<Lit> const & vec) {
    return thandler->assertLits(vec);
}

void SingleInterpolationComputationContext::initTSolver() {
    auto const & leaves_ids = proofGraph.getLeaves();
    assert(not leaves_ids.empty());
    for (auto id : leaves_ids) {
        ProofNode * node = proofGraph.getNode(id);
        assert(node);
        assert(isLeafClauseType(node->getType()));
        if (node->getType() != clause_type::CLA_THEORY) { continue; }
        const auto & clause = proofGraph.getNode(id)->getClause();
        for (auto const & lit : clause) {
            Var v = var(lit);
            PTRef atom = this->varToPTRef(v);
            assert(logic.isTheoryTerm(atom));
            thandler->declareAtom(atom);
        }
    }
}

bool SingleInterpolationComputationContext::verifyPartialInterpolant(ProofNode const & n) {
    if(verbose())
        std::cout << "; Verifying partial interpolant" << '\n';
    bool res = verifyPartialInterpolantA(n);
    if(!res)
    {
        assert(false);
        throw OsmtInternalException("Partial interpolant soundness does not hold for A");
    }
    res = verifyPartialInterpolantB(n);
    if(!res)
    {
        assert(false);
        throw OsmtInternalException("Partial interpolant soundness does not hold for B");
    }
    if(verbose())
        std::cout << "; Partial interpolant is sound" << '\n';
    return res;
}

bool SingleInterpolationComputationContext::verifyPartialInterpolantA(ProofNode const & n) {
    // Check A /\ ~(C|a,ab) -> I, i.e., A /\ ~(C|a,ab) /\ ~I unsat
    std::vector<Lit> const & cl = n.getClause();
    vec<PTRef> restricted_clause;

    for (Lit l : cl) {
        Var v = var(l);
        icolor_t var_class = getVarClass(v);
        assert(var_class == icolor_t::I_B || var_class == icolor_t::I_A || var_class == icolor_t::I_AB);
        icolor_t var_color = var_class == icolor_t::I_B || var_class == icolor_t::I_A ? var_class
                                                                                      : getSharedVarColorInNode(v, n);
        if (var_color == icolor_t::I_A || var_color == icolor_t::I_AB) {
            PTRef ptaux = varToPTRef(v);
            if (sign(l)) {
                ptaux = logic.mkNot(ptaux);
            }
            restricted_clause.push(ptaux);
        }
    }

    PTRef cl_ptref = logic.mkNot(logic.mkOr(std::move(restricted_clause)));
    PTRef implicant = logic.mkAnd({pmanager.getPartition(A_mask, PartitionManager::part::A), cl_ptref});

    bool res = VerificationUtils(logic).impliesInternal(implicant, getPartialInterpolant(n));
    assert(res);
    return res;
}

bool SingleInterpolationComputationContext::verifyPartialInterpolantB(ProofNode const & n) {
    // Check B /\ ~(C|b,ab) -> ~I, i.e., B /\ ~(C|b,ab) /\ I unsat
    std::vector<Lit> const & cl = n.getClause();
    vec<PTRef> restricted_clause;

    for (Lit l : cl) {
        Var v = var(l);
        icolor_t var_class = getVarClass(v);
        assert(var_class == icolor_t::I_B || var_class == icolor_t::I_A || var_class == icolor_t::I_AB);
        icolor_t var_color = var_class == icolor_t::I_B || var_class == icolor_t::I_A ? var_class
                                                                                      : getSharedVarColorInNode(v, n);
        if (var_color == icolor_t::I_B || var_color == icolor_t::I_AB) {
            PTRef ptaux = varToPTRef(v);
            if (sign(l)) {
                ptaux = logic.mkNot(ptaux);
            }
            restricted_clause.push(ptaux);
        }
    }

    PTRef cl_ptref = logic.mkNot(logic.mkOr(std::move(restricted_clause)));
    PTRef implicant = logic.mkAnd(pmanager.getPartition(A_mask, PartitionManager::part::B), cl_ptref);

    bool res = VerificationUtils(logic).impliesInternal(implicant, logic.mkNot(getPartialInterpolant(n)));
    assert(res);
    return res;
}


SingleInterpolationComputationContext::SingleInterpolationComputationContext(
        const SMTConfig & config,
        Theory & theory,
        TermMapper & termMapper,
        PartitionManager & pmanager,
        const ProofGraph & proof,
        const ipartitions_t & A_mask
) : logic(theory.getLogic()), config(config), pmanager(pmanager), proofGraph(proof), thandler(new THandler(theory, termMapper)), A_mask(A_mask) {
    auto const & vars = proof.getVariables();
    std::size_t varCounts = (*std::max_element(vars.begin(), vars.end())) + 1;
    nodeData.resize(proof.getGraphSize());
    AB_vars_mapping.resize(varCounts, -3);

    // NOTE class A has value -1, class B value -2, undetermined value -3, class AB has index bit from 0 onwards
    int AB_bit_index = 0;
    for (Var v: vars) {
        icolor_t v_class = this->getVarClass(v);
        if (v_class == icolor_t::I_A) { AB_vars_mapping[v] = -1; }
        else if (v_class == icolor_t::I_B) { AB_vars_mapping[v] = -2; }
        else if (v_class == icolor_t::I_AB) {
            AB_vars_mapping[v] = AB_bit_index;
            AB_bit_index++;
        }
        else throw OsmtInternalException("Error in computing variable colors");
    }
    initTSolver();
}


/**************** MAIN INTERPOLANTS GENERATION METHODS ************************/

PTRef SingleInterpolationComputationContext::produceSingleInterpolant() {

    // Check
    checkInterAlgo();

    // Clause and partial interpolant
    ProofNode *n = nullptr;
    PTRef partial_interp = PTRef_Undef;

    // Vector for topological ordering
    std::vector<clauseid_t> DFSv = proofGraph.topolSortingTopDown();
    size_t proof_size = DFSv.size();

    if (verbose() > 0) std::cerr << "; Generating interpolant " << std::endl;

    auto PSFunction = needProofStatistics() ? computePSFunction() : nullptr;

    // Traverse proof and compute current interpolant
    for ( size_t i = 0 ; i < proof_size ; i++ )
    {
        n = proofGraph.getNode(DFSv[i]);
        assert(n);

        // Generate partial interpolant for clause i
        if (n->isLeaf())
        {
            if (!isLeafClauseType(n->getType())) throw OsmtInternalException("; Leaf node with non-leaf clause type");

            labelLeaf(*n, PSFunction.get());

            if (n->getType() == clause_type::CLA_ORIG)
            {
                partial_interp = computePartialInterpolantForOriginalClause(*n);
            }
            else if (n->getType() == clause_type::CLA_THEORY) {
                partial_interp = computePartialInterpolantForTheoryClause(*n);
            }
            else if (n->getType() == clause_type::CLA_SPLIT) {
                partial_interp = computePartialInterpolantForSplitClause(*n);
            }
            else {
                assert(n->getType() == clause_type::CLA_ASSUMPTION);
                // MB: Frame literals must be ignored when interpolating
                // This interpolant will be ignored eventually, any value would do
                setPartialInterpolant(*n, logic.getTerm_true());
                continue;
            }

            assert ( partial_interp != PTRef_Undef );
            setPartialInterpolant(*n, partial_interp);
            if (enabledPedInterpVerif()) {
                verifyPartialInterpolant(*n);
            }
        }
        else { // Inner node
            partial_interp = compInterpLabelingInner(*n);
            assert (partial_interp != PTRef_Undef);
            setPartialInterpolant(*n, partial_interp);
        }
    }

    PSFunction.release();

    PTRef rootInterpolant = getPartialInterpolant(*proofGraph.getRoot());
    assert(rootInterpolant != PTRef_Undef);
    // Last clause visited is the empty clause with total interpolant
    assert(partial_interp == rootInterpolant);

    if (verbose()) {
        //getComplexityInterpolant(partial_interp);
        int nbool, neq, nuf, nif;
        logic.collectStats(partial_interp, nbool, neq, nuf, nif);
        std::cerr << "; Number of boolean connectives: " << nbool << '\n';
        std::cerr << "; Number of equalities: " << neq << '\n';
        std::cerr << "; Number of uninterpreted functions: " << nuf << '\n';
        std::cerr << "; Number of interpreted functions: " << nif << '\n';
    }

    if (verbose() > 1) {
        std::cout << "; Interpolant:\n" << logic.printTerm(rootInterpolant) << '\n';
    }
    return rootInterpolant;
}

/********** FULL LABELING BASED INTERPOLATION **********/



void SingleInterpolationComputationContext::labelLeaf(ProofNode & n, std::map<Var, icolor_t> const * PSFunction) {
    // Proof Sensitive
    if (usingPSInterpolation()) setLeafPSLabeling (n, *PSFunction);
    else if (usingPSWInterpolation()) setLeafPSWLabeling (n, *PSFunction);
    else if (usingPSSInterpolation()) setLeafPSSLabeling (n, *PSFunction);
        // McMillan's system
    else if ( usingMcMillanInterpolation( ) ) setLeafMcMillanLabeling ( n );
        // Symmetric system
    else if ( usingPudlakInterpolation( ) ) setLeafPudlakLabeling ( n );
        // McMillan's prime system
    else if ( usingMcMillanPrimeInterpolation( ) ) setLeafMcMillanPrimeLabeling ( n );
        // Error
    else throw OsmtApiException("No interpolation algorithm chosen");
}

std::vector<Lit> SingleInterpolationComputationContext::getRestrictedNodeClause(ProofNode const & node, icolor_t wantedVarClass) const {
    std::vector<Lit> restrictedClause;
    for (Lit l : node.getClause()) {
        if (proofGraph.isAssumedLiteral(~l)) {
            // ignore if the negation is assumed, it's as if this literal did not exist
            continue;
        }
        Var v = var(l);
        icolor_t var_class = getVarClassFromCache(v);
        assert(var_class == icolor_t::I_B or var_class == icolor_t::I_A or var_class == icolor_t::I_AB);

        icolor_t var_color = var_class == icolor_t::I_B or var_class == icolor_t::I_A ? var_class
                                                                                      : getSharedVarColorInNode(v, node);
        if (var_color == wantedVarClass) restrictedClause.push_back(l);
    }
    return restrictedClause;
}

PTRef SingleInterpolationComputationContext::getInterpolantForOriginalClause(const ProofNode & node, icolor_t clauseClass) const {
    if (clauseClass != icolor_t::I_A and clauseClass != icolor_t::I_B) { throw OsmtInternalException("Unexpected class"); }
    auto otherClass = clauseClass == icolor_t::I_A ? icolor_t::I_B : icolor_t::I_A;
    bool clauseIsA = clauseClass == icolor_t::I_A;

    std::vector<Lit> restricted_clause = getRestrictedNodeClause(node, otherClass);
    if (restricted_clause.empty()) {
        return clauseIsA ? logic.getTerm_false() : logic.getTerm_true();
    }
    vec<PTRef> args; args.capacity(restricted_clause.size());
    for (Lit l : restricted_clause) {
        PTRef litTerm = varToPTRef(var(l));
        if (sign(l) == clauseIsA) litTerm = logic.mkNot(litTerm);
        args.push(litTerm);
    }
    return clauseClass == icolor_t::I_A ? logic.mkOr(std::move(args)) : logic.mkAnd(std::move(args));
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef SingleInterpolationComputationContext::computePartialInterpolantForOriginalClause(ProofNode const & n) const {
    assert(n.getType() == clause_type::CLA_ORIG);
    icolor_t clause_color = getClauseColor(n.getClauseRef());
    if (clause_color == icolor_t::I_AB) {
        // Think of a heuristic for choosing the partition?
        clause_color = icolor_t::I_A;
    }
    // Original leaves can be only of class A or B
    assert(clause_color == icolor_t::I_A || clause_color == icolor_t::I_B);
    PTRef partial_interp = getInterpolantForOriginalClause(n, clause_color);
    assert (partial_interp != PTRef_Undef);
    return partial_interp;
}

PTRef SingleInterpolationComputationContext::computePartialInterpolantForTheoryClause(ProofNode const & n) {
    backtrackTSolver();
    vec<Lit> newvec;
    std::vector<Lit> const & oldvec = n.getClause();
    for (Lit l : oldvec) {
        newvec.push(~l);
    }
    bool satisfiable = this->assertLiteralsToTSolver(newvec);
    if (satisfiable) {
        TRes tres = thandler->check(true);
        satisfiable = (tres != TRes::UNSAT);
    }
    if (satisfiable) {
        assert(false);
        throw OsmtInternalException("Asserting negation of theory clause did not result in conflict in theory solver!");
    }
    std::map<PTRef, icolor_t, std::greater<PTRef>> ptref2label;
    for (Lit l : oldvec) {
        ptref2label.insert({varToPTRef(var(l)), getVarColor(n, var(l))});
    }

    PTRef interpolant = thandler->getInterpolant(A_mask, &ptref2label, pmanager);
    backtrackTSolver();
    return interpolant;
}

/*
 * We treat split clauses as original clauses, but we need to determine the color of the clause.
 * Currently we only support binary split clauses from LIA, in this case we know the split is on an expression
 * already present in the original formula (=> no mixed literals). Thus, we take the color of the clause as the common
 * color of both literals. If one literal is colored A and the other one B, then the split expression is actually common
 * to both A and B. Thus we can consider the clause as A or as B and the interpolant condition on common variables
 * will be preserved.
 */
PTRef SingleInterpolationComputationContext::computePartialInterpolantForSplitClause(const ProofNode & n) const {
    auto const & clause = n.getClause();
    assert(clause.size() == 2); // only binary splits at the moment
    auto clauseColor = getVarClass(var(clause[0])) & getVarClass(var(clause[1]));
    if (clauseColor == icolor_t::I_AB) {
        clauseColor = icolor_t::I_A; // MB: Arbitrary choice, same as with original AB-clauses
    } else if (clauseColor == icolor_t::I_UNDEF) {
        clauseColor = icolor_t::I_A; // MB: Split expression is common, we treat the clause as AB-clause
    }
    if (clauseColor != icolor_t::I_A and clauseColor != icolor_t::I_B) {
        assert(false);
        throw OsmtInternalException("Error in coloring split clause!");
    }
    // Compute interpolant the same way as for original clause
    return getInterpolantForOriginalClause(n, clauseColor);
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef SingleInterpolationComputationContext::compInterpLabelingInner(ProofNode & n) {
    PTRef partial_interp_ant1 = getPartialInterpolant(*n.getAnt1());
    PTRef partial_interp_ant2 = getPartialInterpolant(*n.getAnt2());
    assert (partial_interp_ant1 != PTRef_Undef);
    assert (partial_interp_ant2 != PTRef_Undef);

    // Determine color pivot, depending on its color in the two antecedents
    icolor_t pivot_color = getPivotColor(n);
    if (pivot_color == icolor_t::I_S) {
        Var v = n.getPivot();
        Lit pos = mkLit(v);
        if (proofGraph.isAssumedLiteral(pos)) {
            // Positive occurence of assumed literal is in first parent => return interpolant from second
            return partial_interp_ant2;
        }
        else {
            assert(proofGraph.isAssumedLiteral(~pos));
            return partial_interp_ant1;
        }
    }
    // Pivot colored a -> interpolant = interpolant of ant1 OR interpolant of ant2
    if (pivot_color == icolor_t::I_A) {
        return logic.mkOr(partial_interp_ant1, partial_interp_ant2);
    }
        // Pivot colored b -> interpolant = interpolant of ant1 AND interpolant of ant2
    else if (pivot_color == icolor_t::I_B) {
        return logic.mkAnd(partial_interp_ant1, partial_interp_ant2);
    }
        // Pivot colored ab -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
        // Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
    else if (pivot_color == icolor_t::I_AB) {
        // Find pivot occurrences in ant1 and ant2 and create enodes
        Var piv_ = n.getPivot();
        PTRef piv = varToPTRef(piv_);
        bool choose_alternative = usingAlternativeInterpolant() ? decideOnAlternativeInterpolation(partial_interp_ant1, partial_interp_ant2, logic) : false;
        if (choose_alternative) { // Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
            PTRef and_1 = logic.mkAnd(partial_interp_ant1, logic.mkNot(piv));
            PTRef and_2 = logic.mkAnd(partial_interp_ant2, piv);
            return logic.mkOr(and_1, and_2);
        } else { // Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
            PTRef or_1 = logic.mkOr(partial_interp_ant1, piv);
            PTRef or_2 = logic.mkOr(partial_interp_ant2, logic.mkNot(piv));
            return logic.mkAnd(or_1, or_2);
        }
    } else throw OsmtInternalException("Pivot has no color");
}

template<typename TFun>
void SingleInterpolationComputationContext::setLeafLabeling(ProofNode & node, TFun colorABVar) {
    resetLabeling(node);
    std::vector<Lit> const & cl = node.getClause();

    for (Lit l : cl) {
        Var v = var (l);
        icolor_t var_class = getVarClassFromCache(v);
        if (var_class == icolor_t::I_AB) {
            colorABVar(node, v);
        } else if ( var_class != icolor_t::I_A and var_class != icolor_t::I_B ) {
            OsmtInternalException("Variable has no class");
        }
    }
}

void SingleInterpolationComputationContext::setLeafPSLabeling (ProofNode & n, std::map<Var, icolor_t> const & labels) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        auto it = labels.find(v);
        if (it->second == icolor_t::I_A)
            colorA(node, v);
        else
            colorB(node, v);
    });
}

void SingleInterpolationComputationContext::setLeafPSWLabeling(ProofNode & n, std::map<Var, icolor_t> const & labels) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        auto it = labels.find(v);
        if (it->second == icolor_t::I_A)
            colorA(node, v);
        else
            colorAB(node, v);
    });
}

void SingleInterpolationComputationContext::setLeafPSSLabeling(ProofNode & n, std::map<Var, icolor_t> const & labels) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        auto it = labels.find(v);
        if (it->second == icolor_t::I_A)
            colorAB(node, v);
        else
            colorB(node, v);
    });
}

void SingleInterpolationComputationContext::setLeafPudlakLabeling(ProofNode & n) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        colorAB(node, v);
    });
}

void SingleInterpolationComputationContext::setLeafMcMillanLabeling(ProofNode & n) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        colorB(node, v);
    });
}

void SingleInterpolationComputationContext::setLeafMcMillanPrimeLabeling(ProofNode & n) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        colorA(node, v);
    });
}

/************************ INTERPOLATION CONTEXT ************************************************************/

InterpolationContext::InterpolationContext(SMTConfig & c, Theory & th, TermMapper & termMapper, Proof const & proof,
                                           PartitionManager & pmanager)
        : config(c), theory(th), termMapper(termMapper), logic(th.getLogic()), pmanager(pmanager),
          proof_graph{new ProofGraph(c, th.getLogic(), termMapper, proof)} {
    ensureNoLiteralsWithoutPartition();
    if (c.proof_reduce()) {
        reduceProofGraph();
    }

    if (c.proof_interpolant_cnf() > 0) { // Proof restructuring for generation of interpolants in CNF
        transformProofForCNFInterpolants();
    }
}

InterpolationContext::~InterpolationContext() = default;

void InterpolationContext::printProofDotty() {
    assert(proof_graph);
    proof_graph->printProofGraph();
}

void InterpolationContext::getSingleInterpolant(vec<PTRef> & interpolants, const ipartitions_t & A_mask) {
    assert(proof_graph);
    PTRef itp = SingleInterpolationComputationContext(config, theory, termMapper, pmanager, *proof_graph, A_mask).produceSingleInterpolant();

    if (enabledInterpVerif()) {
        bool sound = verifyInterpolant(itp, A_mask);
        assert(sound);
        if (verbose()) {
            if (sound) std::cout << "; Final interpolant is sound" << '\n';
            else std::cout << "; Final interpolant is NOT sound" << '\n';
        }
    }

    if (config.simplify_inter() > 0) {
        itp = simplifyInterpolant(itp);
    }
    interpolants.push(itp);
}

void InterpolationContext::getSingleInterpolant(std::vector<PTRef> & interpolants, const ipartitions_t & A_mask) {
    vec<PTRef> itps;
    getSingleInterpolant(itps, A_mask);
    for (int i = 0; i < itps.size(); i++) interpolants.push_back(itps[i]);
}

bool InterpolationContext::getPathInterpolants(vec<PTRef> & interpolants, const std::vector<ipartitions_t> & A_masks) {
    assert(proof_graph);
    bool propertySatisfied = true;
    // check that masks are subset of each other
    assert(std::mismatch(A_masks.begin() + 1, A_masks.end(), A_masks.begin(), [](auto const & next, auto const & previous){
        return (previous & next) == previous;
    }).first == A_masks.end());

    for (unsigned i = 0; i < A_masks.size(); ++i) {
        getSingleInterpolant(interpolants, A_masks[i]);
        if (i > 0 and enabledInterpVerif()) {
            PTRef previous_itp = interpolants[interpolants.size() - 2];
            PTRef next_itp = interpolants[interpolants.size() - 1];
            PTRef movedPartitions = logic.mkAnd(pmanager.getPartitions(A_masks[i] ^ A_masks[i - 1]));
            propertySatisfied &= VerificationUtils(logic).impliesInternal(logic.mkAnd(previous_itp, movedPartitions), next_itp);
            if (not propertySatisfied) {
                std::cerr << "; Path interpolation does not hold for:\n"
                          << "First interpolant: " << logic.printTerm(previous_itp) << '\n'
                          << "Moved partitions: " << logic.printTerm(movedPartitions) << '\n'
                          << "Second interpolant: " << logic.printTerm(next_itp) << '\n';
            }
        }
    }
    assert(propertySatisfied);
    return propertySatisfied;
}

void InterpolationContext::reduceProofGraph() {
    assert(proof_graph);
    proof_graph->transfProofForReduction();
}

void InterpolationContext::transformProofForCNFInterpolants() {
    throw std::logic_error("Not supported at the moment");
    assert(proof_graph);
    if (usingMcMillanInterpolation()) {
        proof_graph->transfProofForCNFInterpolants([](Var) { return icolor_t::I_UNDEF; }); // FIXME: this requires partition mask and can be done only for single interpolant computation
    } else {
        std::cerr << "; Warning!\n"
                  << "; Please set McMillan interpolation algorithm to generate interpolants in CNF";
    }
}

bool InterpolationContext::verifyInterpolant(PTRef itp, const ipartitions_t & A_mask) const {
    PTRef partA = pmanager.getPartition(A_mask, PartitionManager::part::A);
    PTRef partB = pmanager.getPartition(A_mask, PartitionManager::part::B);
    bool sound = VerificationUtils(logic).verifyInterpolantInternal(partA, partB, itp);
    return sound;
}

PTRef InterpolationContext::simplifyInterpolant(PTRef itp) const {
    const bool cannotSimplify = not logic.isBooleanOperator(itp) or logic.isNot(itp);
    if (cannotSimplify) { return itp; }

    auto simplificationLevel = config.simplify_inter();
    if(simplificationLevel == 4) {
        itp = ::rewriteMaxArityAggresive(logic, itp);
        itp = ::simplifyUnderAssignment_Aggressive(itp, logic);
    }
    else {
        if (simplificationLevel > 0) {
            if (verbose() > 1) {
                std::cout << "Itp before rewriting max arity: \n" << logic.printTerm(itp) << "\n\n";
            }
            itp = ::rewriteMaxArityClassic(logic, itp);
        }
        if (simplificationLevel == 2) {
            if (verbose() > 1) {
                std::cout << "Itp before aggressive simplifying: \n" << logic.printTerm(itp) << "\n\n";
            }
            itp = ::simplifyUnderAssignment(logic, itp);
        }

        if (simplificationLevel == 3) {
            if (verbose() > 1) {
                std::cout << "Itp before aggressive simplifying: \n" << logic.printTerm(itp) << "\n\n";
            }
            itp = ::simplifyUnderAssignment_Aggressive(itp, logic);
        }
    }
    return itp;
}

void InterpolationContext::ensureNoLiteralsWithoutPartition() {
    std::vector<Var> noPartitionVars;
    for (Var v : proof_graph->getVariables()) {
        auto const& part = pmanager.getIPartitions(termMapper.varToPTRef(v));
        if(part == 0 && not proof_graph->isAssumedVar(v)) {
            PTRef term = termMapper.varToPTRef(v);
            assert(this->logic.isTheoryTerm(term));
            auto allowedPartitions = pmanager.computeAllowedPartitions(term);
            if (allowedPartitions != 0) {
                // MB: Update the partition information
                pmanager.addIPartitions(term, allowedPartitions);
            }
            else {
                noPartitionVars.push_back(v);
            }
        }
    }
    if (!noPartitionVars.empty()) {
        proof_graph->eliminateNoPartitionTheoryVars(noPartitionVars);
    }
}

