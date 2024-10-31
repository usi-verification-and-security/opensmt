#ifndef OPENSMT_UNSATCOREBUILDER_H
#define OPENSMT_UNSATCOREBUILDER_H

#include "UnsatCore.h"

#include <minisat/core/SolverTypes.h>
#include <options/SMTConfig.h>

#include <memory>
#include <vector>

namespace opensmt {

class UnsatCore;

class MainSolver;

class Logic;
class ResolutionProof;
class PartitionManager;

class UnsatCoreBuilderBase {
public:
    using Proof = ResolutionProof;

    UnsatCoreBuilderBase(MainSolver const &);

protected:
    MainSolver const & solver;
    SMTConfig const & config;
    Logic & logic;
    Proof const & proof;
    PartitionManager const & partitionManager;
};

class UnsatCoreBuilder : public UnsatCoreBuilderBase {
public:
    UnsatCoreBuilder(MainSolver const & solver_) : UnsatCoreBuilderBase(solver_) {}

    std::unique_ptr<UnsatCore> build();

protected:
    class Minimize;

    void buildBody();
    std::unique_ptr<UnsatCore> buildReturn();

    void computeClauses();
    void mapClausesToTerms();

    void partitionNamedTerms();

    void minimize();

    vec<CRef> clauses{};
    vec<PTRef> allTerms{};
    vec<PTRef> namedTerms{};
    vec<PTRef> hiddenTerms{};
};

class UnsatCoreBuilder::Minimize {
public:
    using InternalSMTSolver = MainSolver;

    Minimize(UnsatCoreBuilder &, vec<PTRef> targetTerms, vec<PTRef> const & backgroundTerms_ = {});
    ~Minimize();

    vec<PTRef> perform() &&;

protected:
    SMTConfig makeSmtSolverConfig() const;
    std::unique_ptr<InternalSMTSolver> newSmtSolver(SMTConfig &) const;

    vec<PTRef> performNaive(InternalSMTSolver &);

    UnsatCoreBuilder & builder;

    vec<PTRef> targetTerms;
    vec<PTRef> const & backgroundTerms;
};

} // namespace opensmt

#endif // OPENSMT_UNSATCOREBUILDER_H
