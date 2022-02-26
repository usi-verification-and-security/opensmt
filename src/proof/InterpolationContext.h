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
    SMTConfig & config;
    Theory & theory;
    TermMapper & termMapper;
    Logic & logic;
    PartitionManager & pmanager;
    std::unique_ptr<ProofGraph> proof_graph;
public:
    InterpolationContext(SMTConfig & c, Theory & th, TermMapper & termMapper, Proof const & t,
                         PartitionManager& pmanager , int n = -1 );
    ~InterpolationContext();

    void printProofDotty();

    // Create interpolants with each A consisting of the specified partitions
    void getInterpolants(const std::vector<vec<int> > & partitions, vec<PTRef> & interpolants);

    void getSingleInterpolant(vec<PTRef> & interpolants, const ipartitions_t & A_mask);

    void getSingleInterpolant(std::vector<PTRef>& interpolants, const ipartitions_t& A_mask);

    bool getPathInterpolants(vec<PTRef> & interpolants, const std::vector<ipartitions_t> & A_masks);

private:
    void reduceProofGraph();

    void transformProofForCNFInterpolants();

    bool verifyInterpolant(PTRef itp, ipartitions_t const & A_mask) const;

    PTRef simplifyInterpolant(PTRef itp) const;

    void ensureNoLiteralsWithoutPartition();

    /***** CONFIGURATION ****/

    int verbose() const { return config.verbosity(); }

    bool usingMcMillanInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_mcmillan; }

    bool usingPudlakInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_pudlak; }

    bool usingMcMillanPrimeInterpolation() const {
        return config.getBooleanInterpolationAlgorithm() == itp_alg_mcmillanp;
    }

    bool usingPSInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_ps; }

    bool usingPSWInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_psw; }

    bool usingPSSInterpolation() const { return config.getBooleanInterpolationAlgorithm() == itp_alg_pss; }

    bool enabledInterpVerif() const { return (config.certify_inter() >= 1); }
};


#endif //OPENSMT_INTERPOLATIONCONTEXT_H
