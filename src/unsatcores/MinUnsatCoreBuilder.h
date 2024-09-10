#ifndef OPENSMT_MINUNSATCOREBUILDER_H
#define OPENSMT_MINUNSATCOREBUILDER_H

#include "UnsatCoreBuilder.h"

namespace opensmt {

class MainSolver;

class MinUnsatCoreBuilder : public UnsatCoreBuilder {
public:
    using SMTSolver = MainSolver;

    MinUnsatCoreBuilder(SMTConfig const & conf, Proof const & proof_, PartitionManager const & pmanager,
                        TermNames const & names, std::unique_ptr<SMTSolver> && smtSolver)
        : UnsatCoreBuilder(conf, proof_, pmanager, names),
          smtSolverPtr{std::move(smtSolver)} {}

    std::unique_ptr<UnsatCore> build();

protected:
    void buildBody();

    void minimize();

    void minimizeInit();
    void minimizeAlg() { minimizeAlgNaive(); }
    void minimizeFinish() {}

    void minimizeAlgNaive();

    std::unique_ptr<SMTSolver> smtSolverPtr;
};

} // namespace opensmt

#endif // OPENSMT_MINUNSATCOREBUILDER_H
