/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

Periplo -- Copyright (C) 2013, Simone Fulvio Rollini

Periplo is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Periplo is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Periplo. If not, see <http://www.gnu.org/licenses/>.
 *********************************************************************/

#include "PG.h"

#include "OsmtInternalException.h"
#include "VerificationUtils.h"

#include <iostream>

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

namespace {
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
                auto const & clause = n->getClause();
                assert(clause.size() == 2); // only binary splits at the moment
                auto color = getVarColor(*n, var(clause[0]));
                assert(color == getVarColor(*n, var(clause[1]))); // same theory variables in the atoms of the split => same color
                assert(color == icolor_t::I_A || color == icolor_t::I_B || color == icolor_t::I_AB);
                // If split on A-local (B-local) term, then return False (True). This is the same as in purely propoositional case.
                // If split on AB-shared term, we can choose if we treat it as A-clause (resulting in False) or B-clause (resulting in True). We arbitrarily choose A now.
                partial_interp = color == icolor_t::I_A ? logic.getTerm_false() : (color == icolor_t::I_B ? logic.getTerm_true() : logic.getTerm_false());
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
    std::map<PTRef, icolor_t> ptref2label;
    for (Lit l : oldvec) {
        ptref2label.insert({varToPTRef(var(l)), getVarColor(n, var(l))});
    }

    PTRef interpolant = thandler->getInterpolant(A_mask, &ptref2label, pmanager);
    backtrackTSolver();
    return interpolant;
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

// HELPER methods for theory solver
void SingleInterpolationComputationContext::backtrackTSolver() {
    thandler->backtrack(-1);
}

bool SingleInterpolationComputationContext::assertLiteralsToTSolver(vec<Lit> const & vec) {
    return thandler->assertLits(vec);
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

    for (Lit l: cl) {
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

    bool res = VerificationUtils(config, logic).impliesExternal(implicant, getPartialInterpolant(n));
    assert(res);
    return res;
}

bool SingleInterpolationComputationContext::verifyPartialInterpolantB(ProofNode const & n) {
    // Check B /\ ~(C|b,ab) -> ~I, i.e., B /\ ~(C|b,ab) /\ I unsat
    std::vector<Lit> const & cl = n.getClause();
    vec<PTRef> restricted_clause;

    for (Lit l: cl) {
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

    bool res = VerificationUtils(config, logic).impliesExternal(implicant, logic.mkNot(getPartialInterpolant(n)));
    assert(res);
    return res;
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
    nodeData.clear();
    AB_vars_mapping.clear();
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
