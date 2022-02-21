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

InterpolationContext::InterpolationContext(SMTConfig & c, Theory & th, TermMapper & termMapper, Proof const & t,
                                           PartitionManager & pmanager, int n)
                                           : logic(th.getLogic()), pmanager(pmanager), config(c),
                                           proof_graph{new ProofGraph(c, th, termMapper, t, pmanager, n)} {
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
    proof_graph->produceSingleInterpolant(interpolants, A_mask);

    if (enabledInterpVerif()) {
        assert(interpolants.size() > 0);
        bool sound = verifyInterpolant(interpolants.last(), A_mask);
        assert(sound);
        if (verbose()) {
            if (sound) std::cout << "; Final interpolant is sound" << '\n';
            else std::cout << "; Final interpolant is NOT sound" << '\n';
        }
    }

    if (config.simplify_inter() > 0) {
        interpolants.last() = simplifyInterpolant(interpolants.last());
    }
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
            propertySatisfied &= VerificationUtils(config, logic).impliesExternal(logic.mkAnd(previous_itp, movedPartitions), next_itp);
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
    assert(proof_graph);
    if (usingMcMillanInterpolation()) {
        proof_graph->transfProofForCNFInterpolants();
    } else {
        std::cerr << "; Warning!\n"
                  << "; Please set McMillan interpolation algorithm to generate interpolants in CNF";
    }
}

bool InterpolationContext::verifyInterpolant(PTRef itp, const ipartitions_t & A_mask) const {
    PTRef partA = pmanager.getPartition(A_mask, PartitionManager::part::A);
    PTRef partB = pmanager.getPartition(A_mask, PartitionManager::part::B);
    bool sound = VerificationUtils(config, logic).verifyInterpolantExternal(partA, partB, itp);
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

