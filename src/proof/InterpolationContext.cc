//
// Created by Martin Blicha on 28.09.20.
//

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

// Create interpolants with each A consisting of the specified partitions
void InterpolationContext::getInterpolants(const vec<vec<int> > & partitions, vec<PTRef> & interpolants) {
    assert(proof_graph);
    proof_graph->produceConfigMatrixInterpolants(partitions, interpolants);
}

void InterpolationContext::getInterpolants(const vec<ipartitions_t> & partitions, vec<PTRef> & interpolants) {
    assert(proof_graph);
    proof_graph->produceMultipleInterpolants(partitions, interpolants);
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

bool InterpolationContext::getPathInterpolants(vec<PTRef> & interpolants, const vec<ipartitions_t> & A_masks) {
    assert(proof_graph);
    return proof_graph->producePathInterpolants(interpolants, A_masks);
}

bool InterpolationContext::getPathInterpolants(vec<PTRef> & interpolants) {
    assert(proof_graph);
    return proof_graph->producePathInterpolants(interpolants);
}

bool InterpolationContext::getSimultaneousAbstractionInterpolants(vec<PTRef> & interpolants) {
    assert(proof_graph);
    return proof_graph->produceSimultaneousAbstraction(interpolants);
}

bool InterpolationContext::getGenSimultaneousAbstractionInterpolants(vec<PTRef> & interpolants) {
    assert(proof_graph);
    return proof_graph->produceGenSimultaneousAbstraction(interpolants);
}

bool InterpolationContext::getStateTransitionInterpolants(vec<PTRef> & interpolants) {
    assert(proof_graph);
    return proof_graph->produceStateTransitionInterpolants(interpolants);
}

bool InterpolationContext::getTreeInterpolants(opensmt::InterpolationTree * it, vec<PTRef> & interpolants) {
    assert(proof_graph);
    return proof_graph->produceTreeInterpolants(it, interpolants);
}

void InterpolationContext::reduceProofGraph() {
    assert(proof_graph);
    proof_graph->transfProofForReduction();
}

