#ifndef OPENSMT_UNSATCOREBUILDER_H
#define OPENSMT_UNSATCOREBUILDER_H

#include "UnsatCore.h"

#include <minisat/core/SolverTypes.h>
#include <options/SMTConfig.h>

#include <memory>

namespace opensmt {

class UnsatCore;

class ResolutionProof;
class PartitionManager;

class UnsatCoreBuilder {
public:
    using Proof = ResolutionProof;

    inline UnsatCoreBuilder(SMTConfig const * conf, Proof const * proof, PartitionManager const * pmanager);

    std::unique_ptr<UnsatCore> build();

protected:
    void computeClauses();
    void computeTerms();

    SMTConfig const * configPtr;
    Proof const * proofPtr;
    PartitionManager const * partitionManagerPtr;

private:
    vec<CRef> clauses;
    vec<PTRef> terms;
};

UnsatCoreBuilder::UnsatCoreBuilder(SMTConfig const * conf, Proof const * proof, PartitionManager const * pmanager)
    : configPtr{conf},
      proofPtr{proof},
      partitionManagerPtr{pmanager} {
    assert(conf);
    assert(proof);
    assert(pmanager);
}

} // namespace opensmt

#endif // OPENSMT_UNSATCOREBUILDER_H
