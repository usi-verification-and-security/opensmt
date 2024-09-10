#ifndef OPENSMT_UNSATCOREBUILDER_H
#define OPENSMT_UNSATCOREBUILDER_H

#include "UnsatCore.h"

#include <minisat/core/SolverTypes.h>
#include <options/SMTConfig.h>

#include <memory>
#include <vector>

namespace opensmt {

class UnsatCore;

class Logic;
class ResolutionProof;
class PartitionManager;
class TermNames;

class MainSolver;

class UnsatCoreBuilder {
public:
    using Proof = ResolutionProof;

    UnsatCoreBuilder(SMTConfig const & conf, Logic & logic_, Proof const & proof_, PartitionManager const & pmanager,
                     TermNames const & names)
        : config{conf},
          logic{logic_},
          proof{proof_},
          partitionManager{pmanager},
          termNames{names} {}

    std::unique_ptr<UnsatCore> build();

protected:
    using SMTSolver = MainSolver;

    void buildBody();
    std::unique_ptr<UnsatCore> buildReturn();

    void computeClauses();
    void computeTerms();
    void computeNamedTerms();

    SMTConfig makeSmtSolverConfig() const;
    std::unique_ptr<SMTSolver> newSmtSolver(SMTConfig &) const;

    void minimize();

    void minimizeInit();
    void minimizeAlg() { minimizeAlgNaive(); }
    void minimizeFinish() {}

    void minimizeAlgNaive();

    SMTConfig const & config;
    Logic & logic;
    Proof const & proof;
    PartitionManager const & partitionManager;
    TermNames const & termNames;

    vec<CRef> clauses{};
    vec<PTRef> terms{};
    vec<PTRef> namedTerms{};

    std::vector<size_t> namedTermsIdxs{};
};

} // namespace opensmt

#endif // OPENSMT_UNSATCOREBUILDER_H
