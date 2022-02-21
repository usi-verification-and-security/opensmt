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

#include <iostream>

/**************** MAIN INTERPOLANTS GENERATION METHODS ************************/

void ProofGraph::produceSingleInterpolant ( vec<PTRef> &interpolants, const ipartitions_t &A_mask)
{
    if (verbose()) std::cerr << "; Single interpolant " << '\n';

    // Check
    checkInterAlgo();

    // Track AB class variables and associate index to them in nodes bit masks
    // TODO: Check that the largest node ID is smaller than the graph size? Are there any holes in graph? Does node ID match its position in graph even after transformations?
    interpolationInfo.reset(graph.size(), proof_variables, [&](Var v) {
       return getVarClass(v, A_mask);
    });

    // Clause and partial interpolant
    ProofNode *n = nullptr;
    PTRef partial_interp = PTRef_Undef;

    // Vector for topological ordering
    std::vector< clauseid_t > DFSv;
    // Compute topological sorting of graph
    topolSortingTopDown ( DFSv );
    size_t proof_size = DFSv.size();

    if (verbose() > 0) std::cerr << "; Generating interpolant " << std::endl;

    std::map<Var, icolor_t> *PSFunction = computePSFunction (DFSv, A_mask);

    // Traverse proof and compute current interpolant
    for ( size_t i = 0 ; i < proof_size ; i++ )
    {
        n = getNode ( DFSv[ i ] );
        assert (n);

        // Generate partial interpolant for clause i
        if (n->isLeaf())
        {
            if (!isLeafClauseType(n->getType())) throw OsmtInternalException("; Leaf node with non-leaf clause type");

            labelLeaf(*n, PSFunction);

            if (n->getType() == clause_type::CLA_ORIG)
            {
                partial_interp = computePartialInterpolantForOriginalClause(*n, A_mask);
            }
            else if (n->getType() == clause_type::CLA_THEORY) {
                partial_interp = computePartialInterpolantForTheoryClause(*n, A_mask);
            }
            else if (n->getType() == clause_type::CLA_SPLIT) {
                auto const & clause = n->getClause();
                assert(clause.size() == 2); // only binary splits at the moment
                auto color = getVarColor(*n, var(clause[0]));
                assert(color == getVarColor(*n, var(clause[1]))); // same theory variables in the atoms of the split => same color
                assert(color == icolor_t::I_A || color == icolor_t::I_B || color == icolor_t::I_AB);
                // If split on A-local (B-local) term, then return False (True). This is the same as in purely propoositional case.
                // If split on AB-shared term, we can choose if we treat it as A-clause (resulting in False) or B-clause (resulting in True). We arbitrarily choose A now.
                partial_interp = color == icolor_t::I_A ? logic_.getTerm_false() : (color == icolor_t::I_B ? logic_.getTerm_true() : logic_.getTerm_false());
            }
            else {
                assert(n->getType() == clause_type::CLA_ASSUMPTION);
                // MB: Frame literals must be ignored when interpolating
                // This interpolant will be ignored eventually, any value would do
                interpolationInfo.setPartialInterpolant(*n, logic_.getTerm_true());
                continue;
            }

            assert ( partial_interp != PTRef_Undef );
            interpolationInfo.setPartialInterpolant(*n, partial_interp);
            if (enabledPedInterpVerif()) {
                verifyPartialInterpolant(n, A_mask);
            }
        }
        else { // Inner node
            partial_interp = compInterpLabelingInner(*n);
            assert (partial_interp != PTRef_Undef);
            interpolationInfo.setPartialInterpolant(*n, partial_interp);
        }
    }

    delete PSFunction;

    PTRef rootInterpolant = interpolationInfo.getPartialInterpolant(*getRoot());
    assert(rootInterpolant != PTRef_Undef);
    // Last clause visited is the empty clause with total interpolant
    assert(partial_interp == rootInterpolant);

    if (verbose()) {
        //getComplexityInterpolant(partial_interp);
        int nbool, neq, nuf, nif;
        this->logic_.collectStats(partial_interp, nbool, neq, nuf, nif);
        std::cerr << "; Number of boolean connectives: " << nbool << '\n';
        std::cerr << "; Number of equalities: " << neq << '\n';
        std::cerr << "; Number of uninterpreted functions: " << nuf << '\n';
        std::cerr << "; Number of interpreted functions: " << nif << '\n';
    }

    interpolants.push(rootInterpolant);

    if (verbose() > 1) {
        std::cout << "; Interpolant:\n" << this->logic_.printTerm(rootInterpolant) << '\n';
    }
}

void ProofGraph::checkInterAlgo()
{
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



void ProofGraph::labelLeaf(ProofNode & n, std::map<Var, icolor_t> const * PSFunction) {
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

std::vector<Lit> ProofGraph::getRestrictedNodeClause(ProofNode const & node, icolor_t wantedVarClass) const {
    std::vector<Lit> restrictedClause;
    for (Lit l : node.getClause()) {
        if (isAssumedLiteral(~l)) {
            // ignore if the negation is assumed, it's as if this literal did not exist
            continue;
        }
        Var v = var(l);
        icolor_t var_class = interpolationInfo.getVarClass(v);
        assert(var_class == icolor_t::I_B or var_class == icolor_t::I_A or var_class == icolor_t::I_AB);

        icolor_t var_color = var_class == icolor_t::I_B or var_class == icolor_t::I_A ? var_class
                                                                                      : getSharedVarColorInNode(v, node);
        if (var_color == wantedVarClass) restrictedClause.push_back(l);
    }
    return restrictedClause;
}

PTRef ProofGraph::getInterpolantForOriginalClause(const ProofNode & node, icolor_t clauseClass) const {
    if (clauseClass != icolor_t::I_A and clauseClass != icolor_t::I_B) { throw OsmtInternalException("Unexpected class"); }
    auto otherClass = clauseClass == icolor_t::I_A ? icolor_t::I_B : icolor_t::I_A;
    bool clauseIsA = clauseClass == icolor_t::I_A;

    std::vector<Lit> restricted_clause = getRestrictedNodeClause(node, otherClass);
    if (restricted_clause.empty()) {
        return clauseIsA ? logic_.getTerm_false() : logic_.getTerm_true();
    }
    vec<PTRef> args; args.capacity(restricted_clause.size());
    for (Lit l : restricted_clause) {
        PTRef litTerm = varToPTRef(var(l));
        if (sign(l) == clauseIsA) litTerm = logic_.mkNot(litTerm);
        args.push(litTerm);
    }
    return clauseClass == icolor_t::I_A ? logic_.mkOr(std::move(args)) : logic_.mkAnd(std::move(args));
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::computePartialInterpolantForOriginalClause(ProofNode const & n, ipartitions_t const & A_mask)
{
    assert(n.getType() == clause_type::CLA_ORIG);
    icolor_t clause_color = getClauseColor(n.getClauseRef(), A_mask);
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

PTRef ProofGraph::computePartialInterpolantForTheoryClause(ProofNode const & n, ipartitions_t const & A_mask) {
    clearTSolver();
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
    clearTSolver();
    return interpolant;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingInner(ProofNode & n) {
    PTRef partial_interp_ant1 = interpolationInfo.getPartialInterpolant(*n.getAnt1());
    PTRef partial_interp_ant2 = interpolationInfo.getPartialInterpolant(*n.getAnt2());
    assert (partial_interp_ant1 != PTRef_Undef);
    assert (partial_interp_ant2 != PTRef_Undef);

    // Determine color pivot, depending on its color in the two antecedents
    icolor_t pivot_color = getPivotColor(n);
    if (pivot_color == icolor_t::I_S) {
        Var v = n.getPivot();
        Lit pos = mkLit(v);
        if(isAssumedLiteral(pos)) {
            // Positive occurence of assumed literal is in first parent => return interpolant from second
            return partial_interp_ant2;
        }
        else {
            assert(isAssumedLiteral(~pos));
            return partial_interp_ant1;
        }
    }
    // Pivot colored a -> interpolant = interpolant of ant1 OR interpolant of ant2
    if (pivot_color == icolor_t::I_A) {
        return logic_.mkOr(partial_interp_ant1, partial_interp_ant2);
    }
    // Pivot colored b -> interpolant = interpolant of ant1 AND interpolant of ant2
    else if (pivot_color == icolor_t::I_B) {
        return logic_.mkAnd(partial_interp_ant1, partial_interp_ant2);
    }
    // Pivot colored ab -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
    // Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
    else if (pivot_color == icolor_t::I_AB) {
        // Find pivot occurrences in ant1 and ant2 and create enodes
        Var piv_ = n.getPivot();
        PTRef piv = varToPTRef(piv_);
        bool choose_alternative = usingAlternativeInterpolant() ? decideOnAlternativeInterpolation(n) : false;
        if (choose_alternative) { // Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
            PTRef and_1 = logic_.mkAnd(partial_interp_ant1, logic_.mkNot(piv));
            PTRef and_2 = logic_.mkAnd(partial_interp_ant2, piv);
            return logic_.mkOr(and_1, and_2);
        } else { // Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
            PTRef or_1 = logic_.mkOr(partial_interp_ant1, piv);
            PTRef or_2 = logic_.mkOr(partial_interp_ant2, logic_.mkNot(piv));
            return logic_.mkAnd(or_1, or_2);
        }
    } else throw OsmtInternalException("Pivot has no color");
}

void ProofGraph::setLeafPSLabeling (ProofNode & n, std::map<Var, icolor_t> const & labels) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        auto it = labels.find(v);
        assert (theory_only.find(v) != theory_only.end() || it != labels.end());

        if (it->second == icolor_t::I_A)
            interpolationInfo.colorA(node, v);
        else
            interpolationInfo.colorB(node, v);
    });
}

void ProofGraph::setLeafPSWLabeling(ProofNode & n, std::map<Var, icolor_t> const & labels) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        auto it = labels.find(v);
        assert (theory_only.find(v) != theory_only.end() || it != labels.end());

        if (it->second == icolor_t::I_A)
            interpolationInfo.colorA(node, v);
        else
            interpolationInfo.colorAB(node, v);
    });
}

void ProofGraph::setLeafPSSLabeling(ProofNode & n, std::map<Var, icolor_t> const & labels) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        auto it = labels.find(v);
        assert (theory_only.find(v) != theory_only.end() || it != labels.end());

        if (it->second == icolor_t::I_A)
            interpolationInfo.colorAB(node, v);
        else
            interpolationInfo.colorB(node, v);
    });
}

void ProofGraph::setLeafPudlakLabeling(ProofNode & n) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        interpolationInfo.colorAB(node, v);
    });
}

void ProofGraph::setLeafMcMillanLabeling(ProofNode & n) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        interpolationInfo.colorB(node, v);
    });
}

void ProofGraph::setLeafMcMillanPrimeLabeling(ProofNode & n) {
    setLeafLabeling(n, [&](ProofNode & node, Var v) {
        interpolationInfo.colorA(node, v);
    });
}

// HELPER methods for theory solver
void ProofGraph::clearTSolver() {
    thandler->backtrack(-1);
}

bool ProofGraph::assertLiteralsToTSolver(vec<Lit> const & vec) {
    return thandler->assertLits(vec);
}


