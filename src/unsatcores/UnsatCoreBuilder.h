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
class TermNames;

class UnsatCoreBuilder {
public:
    using Proof = ResolutionProof;

    inline UnsatCoreBuilder(SMTConfig const *, Proof const *, PartitionManager const *, TermNames const *);

    std::unique_ptr<UnsatCore> build();

protected:
    void computeClauses();
    void computeTerms();
    void computeNamedTerms();

    SMTConfig const * configPtr;
    Proof const * proofPtr;
    PartitionManager const * partitionManagerPtr;
    TermNames const * termNamesPtr;

private:
    vec<CRef> clauses;
    vec<PTRef> terms;
    vec<PTRef> namedTerms;
};

UnsatCoreBuilder::UnsatCoreBuilder(SMTConfig const * conf, Proof const * proof, PartitionManager const * pmanager,
                                   TermNames const * names)
    : configPtr{conf},
      proofPtr{proof},
      partitionManagerPtr{pmanager},
      termNamesPtr{names} {
    assert(conf);
    assert(proof);
    assert(pmanager);
    assert(names);
}

} // namespace opensmt

#endif // OPENSMT_UNSATCOREBUILDER_H
