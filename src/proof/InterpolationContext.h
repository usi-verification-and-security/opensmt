/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_INTERPOLATIONCONTEXT_H
#define OPENSMT_INTERPOLATIONCONTEXT_H

#include <memory>

#include "Theory.h"

// forward declaration
class Proof;
class ProofGraph;

class InterpolationContext {
    Logic & logic;
    PartitionManager & pmanager;
    SMTConfig & config;
    std::unique_ptr<ProofGraph> proof_graph;
public:
    InterpolationContext(SMTConfig & c, Theory & th, TermMapper & termMapper, Proof const & t,
                         PartitionManager& pmanager, int n = -1 );
    ~InterpolationContext();

    void printProofDotty();

    void setColoringSuggestions(vec<std::map<PTRef, icolor_t> *> * mp);

    void getSingleInterpolant(vec<PTRef> & interpolants);

    void getSingleInterpolant(vec<PTRef> & interpolants, const ipartitions_t & A_mask);

    void getSingleInterpolant(std::vector<PTRef>& interpolants, const ipartitions_t& A_mask);

    bool getPathInterpolants(vec<PTRef> & interpolants, const std::vector<ipartitions_t> & A_masks);

private:
    void reduceProofGraph();

    bool enabledInterpVerif() const { return (config.certify_inter() >= 1); }

};


#endif //OPENSMT_INTERPOLATIONCONTEXT_H
