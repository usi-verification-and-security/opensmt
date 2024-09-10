
#include "UnsatCoreBuilder.h"

#include <api/MainSolver.h>
#include <api/PartitionManager.h>
#include <common/PartitionInfo.h>
#include <common/TermNames.h>
#include <interpolation/InterpolationUtils.h>
#include <logics/Logic.h>
#include <smtsolvers/ResolutionProof.h>

#include <unordered_set>
#include <vector>

namespace opensmt {

using Partitions = ipartitions_t;

std::unique_ptr<UnsatCore> UnsatCoreBuilder::build() {
    buildBody();
    return buildReturn();
}

void UnsatCoreBuilder::buildBody() {
    computeClauses();
    computeTerms();
    computeNamedTerms();

    if (config.minimal_unsat_cores()) { minimize(); }
}

std::unique_ptr<UnsatCore> UnsatCoreBuilder::buildReturn() {
    // Not using `make_unique` because only UnsatCoreBuilder is a friend of UnsatCore
    return std::unique_ptr<UnsatCore>{new UnsatCore{std::move(terms), std::move(namedTerms)}};
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

void UnsatCoreBuilder::computeTerms() {
    assert(clauses.size() > 0);
    assert(terms.size() == 0);

    Partitions partitions;
    for (CRef cref : clauses) {
        auto const & partition = partitionManager.getClauseClassMask(cref);
        orbit(partitions, partitions, partition);
    }

    terms = partitionManager.getPartitions(partitions);
}

void UnsatCoreBuilder::computeNamedTerms() {
    assert(terms.size() > 0);
    namedTerms.clear();
    namedTermsIdxs.clear();

    if (termNames.empty()) return;

    size_t const termsSize = terms.size();
    for (size_t idx = 0; idx < termsSize; ++idx) {
        PTRef term = terms[idx];
        if (not termNames.contains(term)) { continue; }
        namedTerms.push(term);
        namedTermsIdxs.push_back(idx);
    }
}

SMTConfig UnsatCoreBuilder::makeSmtSolverConfig() const {
    assert(config.minimal_unsat_cores());

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

std::unique_ptr<UnsatCoreBuilder::SMTSolver> UnsatCoreBuilder::newSmtSolver(SMTConfig & newConfig) const {
    assert(config.minimal_unsat_cores());

    return std::make_unique<SMTSolver>(logic, newConfig, "unsat core solver");
}

void UnsatCoreBuilder::minimize() {
    minimizeInit();
    minimizeAlg();
    minimizeFinish();
}

void UnsatCoreBuilder::minimizeInit() {
    assert(terms.size() >= namedTerms.size());
    assert(size_t(namedTerms.size()) == namedTermsIdxs.size());
}

void UnsatCoreBuilder::minimizeAlgNaive() {
    if (namedTerms.size() == 0) return;

    SMTConfig smtSolverConfig = makeSmtSolverConfig();
    std::unique_ptr<SMTSolver> smtSolverPtr = newSmtSolver(smtSolverConfig);

    auto const namedTermsIdxsEnd = namedTermsIdxs.end();
    auto const isNamedTerm = [namedTermsIdxsEnd](size_t idx, auto namedTermsIdxsIt) {
        if (namedTermsIdxsIt == namedTermsIdxsEnd) { return false; }
        assert(idx <= *namedTermsIdxsIt);
        return (idx == *namedTermsIdxsIt);
    };
    decltype(terms) newTerms;
    size_t const termsSize = terms.size();
    for (auto [idx, namedTermsIdxsIt] = std::tuple{size_t{0}, namedTermsIdxs.begin()}; idx < termsSize; ++idx) {
        if (isNamedTerm(idx, namedTermsIdxsIt)) {
            ++namedTermsIdxsIt;
            continue;
        }
        PTRef term = terms[idx];
        smtSolverPtr->insertFormula(term);
        newTerms.push(term);
    }

    decltype(namedTerms) newNamedTerms;
    size_t const namedTermsSize = namedTerms.size();
    for (size_t namedIdx = 0; namedIdx < namedTermsSize; ++namedIdx) {
        smtSolverPtr->push();

        // try to ignore namedTerms[namedIdx]

        for (size_t keptNamedIdx = namedIdx + 1; keptNamedIdx < namedTermsSize; ++keptNamedIdx) {
            PTRef term = namedTerms[keptNamedIdx];
            smtSolverPtr->insertFormula(term);
        }

        sstat const res = smtSolverPtr->check();
        assert(res == s_True || res == s_False);
        bool const isRedundant = (res == s_False);

        smtSolverPtr->pop();

        if (isRedundant) continue;

        // namedTerms[namedIdx] is not redundant - include it

        PTRef term = namedTerms[namedIdx];
        smtSolverPtr->insertFormula(term);
        newTerms.push(term);
        newNamedTerms.push(term);
    }

    terms = std::move(newTerms);
    namedTerms = std::move(newNamedTerms);
}

} // namespace opensmt
