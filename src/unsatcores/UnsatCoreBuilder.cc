
#include "UnsatCoreBuilder.h"

#include <api/MainSolver.h>
#include <api/PartitionManager.h>
#include <common/Partitions.h>
#include <common/TermNames.h>
#include <logics/Logic.h>
#include <smtsolvers/ResolutionProof.h>

#include <unordered_set>
#include <vector>

namespace opensmt {

using Partitions = ipartitions_t;

UnsatCoreBuilderBase::UnsatCoreBuilderBase(MainSolver const & solver_)
    : solver{solver_},
      config{solver_.config},
      logic{solver_.logic},
      proof{solver_.smt_solver->getResolutionProof()},
      partitionManager{solver_.pmanager} {}

std::unique_ptr<UnsatCore> UnsatCoreBuilder::build() {
    buildBody();
    return buildReturn();
}

void UnsatCoreBuilder::buildBody() {
    computeClauses();
    mapClausesToTerms();

    if (not config.print_cores_full()) { partitionNamedTerms(); }

    if (config.minimal_unsat_cores()) { minimize(); }
}

std::unique_ptr<UnsatCore> UnsatCoreBuilder::buildReturn() {
    // Not using `make_unique` because only UnsatCoreBuilder is a friend of *UnsatCore

    if (config.print_cores_full()) { return std::unique_ptr<UnsatCore>{new FullUnsatCore{logic, std::move(allTerms)}}; }

    return std::unique_ptr<UnsatCore>{
        new NamedUnsatCore{solver.getTermNames(), std::move(namedTerms), std::move(hiddenTerms)}};
}

void UnsatCoreBuilder::computeClauses() {
    clauses.clear();

    auto const & derivations = proof.getProof();
    std::vector<CRef> stack;
    stack.push_back(CRef_Undef);
    std::unordered_set<CRef> processed;
    while (not stack.empty()) {
        CRef current = stack.back();
        stack.pop_back();
        if (auto [_, inserted] = processed.insert(current); not inserted) { continue; }
        auto it = derivations.find(current);
        assert(it != derivations.end());
        auto const & derivation = it->second;
        if (derivation.type == clause_type::CLA_ORIG) {
            clauses.push(current);
            continue;
        }
        if (derivation.type == clause_type::CLA_LEARNT) {
            for (CRef premise : derivation.chain_cla) {
                stack.push_back(premise);
            }
        }
    }
}

void UnsatCoreBuilder::mapClausesToTerms() {
    assert(clauses.size() > 0);
    assert(allTerms.size() == 0);

    Partitions partitions;
    for (CRef cref : clauses) {
        auto const & partition = partitionManager.getClauseClassMask(cref);
        orbit(partitions, partitions, partition);
    }

    allTerms = partitionManager.getPartitions(partitions);
}

void UnsatCoreBuilder::partitionNamedTerms() {
    assert(not config.print_cores_full());

    assert(allTerms.size() > 0);
    namedTerms.clear();
    hiddenTerms.clear();

    bool const minCore = config.minimal_unsat_cores();
    // See the comment in `minimize` for why we exclude hidden terms here

    auto const & termNames = solver.getTermNames();
    if (termNames.empty()) {
        if (not minCore) { hiddenTerms = std::move(allTerms); }
        return;
    }

    for (PTRef term : allTerms) {
        if (termNames.contains(term)) {
            namedTerms.push(term);
        } else if (not minCore) {
            hiddenTerms.push(term);
        }
    }

    allTerms.clear();
}

void UnsatCoreBuilder::minimize() {
    assert(config.minimal_unsat_cores());

    if (config.print_cores_full()) {
        allTerms = Minimize{*this, std::move(allTerms)}.perform();
        return;
    }

    // We need to minimize `namedTerms`, but this may not be possible with the current hidden terms:
    // some of them were already removed based on the proof and may prevent removal of some named terms
    // Hence, include all hidden terms from the assertion stack
    // TODO: make more efficient
    auto const & termNames = solver.getTermNames();
    assert(hiddenTerms.size() == 0);
    for (PTRef term : solver.getCurrentAssertionsView()) {
        if (termNames.contains(term)) { continue; }
        hiddenTerms.push(term);
        // (we do not care about `allTerms` any more since the call to `partitionNamedTerms`)
    }

    namedTerms = Minimize{*this, std::move(namedTerms), hiddenTerms}.perform();
}

////////////////////////////////////////////////////////////////////////////////

UnsatCoreBuilder::Minimize::Minimize(UnsatCoreBuilder & builder_, vec<PTRef> targetTerms_,
                                     vec<PTRef> const & backgroundTerms_)
    : builder{builder_},
      targetTerms{std::move(targetTerms_)},
      backgroundTerms{backgroundTerms_} {
    assert(builder.config.minimal_unsat_cores());
}

UnsatCoreBuilder::Minimize::~Minimize() {}

SMTConfig UnsatCoreBuilder::Minimize::makeSmtSolverConfig() const {
    SMTConfig newConfig;
    assert(newConfig.isIncremental());
    assert(newConfig.verbosity() == 0);
    assert(not newConfig.printSuccess());
    assert(not newConfig.produceStats());
    assert(not newConfig.produce_unsat_cores());
    assert(not newConfig.produce_proof());
    assert(not newConfig.produce_inter());

    char const * msg = "ok";
    newConfig.setOption(SMTConfig::o_produce_models, SMTOption(false), msg);
    assert(not newConfig.produce_models());

    return newConfig;
}

std::unique_ptr<UnsatCoreBuilder::Minimize::InternalSMTSolver>
UnsatCoreBuilder::Minimize::newSmtSolver(SMTConfig & newConfig) const {
    return std::make_unique<InternalSMTSolver>(builder.logic, newConfig, "min unsat core solver");
}

vec<PTRef> UnsatCoreBuilder::Minimize::perform() && {
    if (targetTerms.size() == 0) { return std::move(targetTerms); }

    SMTConfig smtSolverConfig = makeSmtSolverConfig();
    std::unique_ptr<InternalSMTSolver> smtSolverPtr = newSmtSolver(smtSolverConfig);

    return performNaive(*smtSolverPtr);
}

vec<PTRef> UnsatCoreBuilder::Minimize::performNaive(InternalSMTSolver & smtSolver) {
    for (PTRef term : backgroundTerms) {
        // the term that we do not care about eliminating -> can be hard-asserted
        smtSolver.insertFormula(term);
    }

    // minimize the contents of `targetTerms` (given the already hard-asserted constraints)

    decltype(targetTerms) newTargetTerms;
    size_t const targetTermsSize = targetTerms.size();
    for (size_t idx = 0; idx < targetTermsSize; ++idx) {
        smtSolver.push();

        // try to ignore targetTerms[idx]

        for (size_t keptIdx = idx + 1; keptIdx < targetTermsSize; ++keptIdx) {
            PTRef term = targetTerms[keptIdx];
            smtSolver.insertFormula(term);
        }

        sstat const res = smtSolver.check();
        assert(res == s_True || res == s_False);
        bool const isRedundant = (res == s_False);

        smtSolver.pop();

        if (isRedundant) continue;

        // targetTerms[idx] is not redundant - include it

        PTRef term = targetTerms[idx];
        smtSolver.insertFormula(term); // can already be hard-asserted
        newTargetTerms.push(term);
    }

    return newTargetTerms;
}

} // namespace opensmt
