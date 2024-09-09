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

    UnsatCoreBuilder(SMTConfig const & conf, Proof const & proof_, PartitionManager const & pmanager,
                     TermNames const & names)
        : config{conf},
          proof{proof_},
          partitionManager{pmanager},
          termNames{names} {}

    std::unique_ptr<UnsatCore> build();

protected:
    void computeClauses();
    void computeTerms();
    void computeNamedTerms();

    SMTConfig const & config;
    Proof const & proof;
    PartitionManager const & partitionManager;
    TermNames const & termNames;

private:
    vec<CRef> clauses;
    vec<PTRef> terms;
    vec<PTRef> namedTerms;
};

} // namespace opensmt

#endif // OPENSMT_UNSATCOREBUILDER_H
