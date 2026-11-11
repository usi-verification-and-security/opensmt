/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_INTERPOLATIONCONTEXT_H
#define OPENSMT_INTERPOLATIONCONTEXT_H

#include <logics/Theory.h>

#include <memory>

namespace opensmt {
// forward declaration
class ResolutionProof;
class ProofGraph;

class InterpolationContext {
public:
    InterpolationContext(SMTConfig & c, Theory & th, TermMapper & termMapper, ResolutionProof const & t,
                         PartitionManager & pmanager);

    ~InterpolationContext();

    void printProofDotty();

    // Create interpolants with each A consisting of the specified partitions
    void getInterpolants(std::vector<vec<int>> const & partitions, vec<PTRef> & interpolants);

    // Returns true on success
    bool getSingleInterpolant(vec<PTRef> & interpolants, ipartitions_t const & A_mask);
    bool getSingleInterpolant(std::vector<PTRef> & interpolants, ipartitions_t const & A_mask);

    // Returns true on success
    bool getPathInterpolants(vec<PTRef> & interpolants, std::vector<ipartitions_t> const & A_masks);

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

    SMTConfig & config;
    Theory & theory;
    TermMapper & termMapper;
    Logic & logic;
    PartitionManager & pmanager;
    std::unique_ptr<ProofGraph> proof_graph;
};
} // namespace opensmt

#endif // OPENSMT_INTERPOLATIONCONTEXT_H
