
#include "UnsatCoreBuilder.h"

#include <api/PartitionManager.h>
#include <common/PartitionInfo.h>
#include <common/TermNames.h>
#include <interpolation/InterpolationUtils.h>
#include <smtsolvers/ResolutionProof.h>

#include <unordered_set>
#include <vector>

namespace opensmt {

using Partitions = ipartitions_t;

std::unique_ptr<UnsatCore> UnsatCoreBuilder::build() {
    computeClauses();
    computeTerms();
    computeNamedTerms();

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

    if (termNames.empty()) return;

    for (PTRef term : terms) {
        if (termNames.contains(term)) { namedTerms.push(term); }
    }
}

} // namespace opensmt
