
#include "UnsatCoreBuilder.h"

#include <api/PartitionManager.h>
#include <common/PartitionInfo.h>
#include <interpolation/InterpolationUtils.h>
#include <smtsolvers/ResolutionProof.h>

#include <unordered_set>
#include <vector>

namespace opensmt {

using Partitions = ipartitions_t;

std::unique_ptr<UnsatCore> UnsatCoreBuilder::build() {
    computeClauses();
    computeTerms();

    // Not using `make_unique` because only UnsatCoreBuilder is a friend of UnsatCore
    return std::unique_ptr<UnsatCore>{new UnsatCore{std::move(terms)}};
}

void UnsatCoreBuilder::computeClauses() {
    clauses.clear();

    auto const & derivations = proofPtr->getProof();
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
        auto const & partition = partitionManagerPtr->getClauseClassMask(cref);
        orbit(partitions, partitions, partition);
    }

    terms = partitionManagerPtr->getPartitions(partitions);
}

} // namespace opensmt
