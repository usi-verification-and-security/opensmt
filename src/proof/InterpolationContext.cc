/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "InterpolationContext.h"

#include "PG.h"

InterpolationContext::InterpolationContext(SMTConfig & c, Theory & th, TermMapper & termMapper, Proof const & t,
                                           PartitionManager & pmanager, int n) : proof_graph{
    new ProofGraph(c, th, termMapper, t, pmanager, n)} {
    if (c.proof_reduce()) {
        reduceProofGraph();
    }
}

InterpolationContext::~InterpolationContext() = default;

void InterpolationContext::printProofDotty() {
    assert(proof_graph);
    proof_graph->printProofGraph();
}


void InterpolationContext::setColoringSuggestions(
    vec<std::map<PTRef, icolor_t> *> * mp) { proof_graph->setColoringSuggestions(mp); }

void InterpolationContext::getSingleInterpolant(vec<PTRef> & interpolants) {
    assert(proof_graph);
    proof_graph->produceSingleInterpolant(interpolants);
}

void InterpolationContext::getSingleInterpolant(vec<PTRef> & interpolants, const ipartitions_t & A_mask) {
    assert(proof_graph);
    proof_graph->produceSingleInterpolant(interpolants, A_mask);
}

void InterpolationContext::getSingleInterpolant(std::vector<PTRef> & interpolants, const ipartitions_t & A_mask) {
    vec<PTRef> itps;
    getSingleInterpolant(itps, A_mask);
    for (int i = 0; i < itps.size(); i++) interpolants.push_back(itps[i]);
}

bool InterpolationContext::getPathInterpolants(vec<PTRef> & interpolants, const std::vector<ipartitions_t> & A_masks) {
    assert(proof_graph);
    return proof_graph->producePathInterpolants(interpolants, A_masks);
}

void InterpolationContext::reduceProofGraph() {
    assert(proof_graph);
    proof_graph->transfProofForReduction();
}

