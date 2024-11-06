/*
 *  Copyright (c) 2020 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "PartitionManager.h"

#include <common/InternalException.h>
#include <common/TreeOps.h>

namespace opensmt {
void PartitionManager::propagatePartitionMask(PTRef root) {
    ipartitions_t & p = getIPartitions(root);
    std::vector<bool> seen;
    // MB: Relies on invariant: Every subterm was created before its parent, so it has lower id
    auto size = Idx(logic.getPterm(root).getId()) + 1;
    seen.resize(size, false);
    std::vector<PTRef> queue{root};
    while (!queue.empty()) {
        PTRef current = queue.back();
        queue.pop_back();
        Pterm const & c_term = logic.getPterm(current);
        auto id = Idx(c_term.getId());
        assert(id < size);
        if (!seen[id]) {
            addIPartitions(current, p);
            for (int j = 0; j < c_term.size(); ++j) {
                queue.push_back(c_term[j]);
            }
            if (logic.isUF(current) || logic.isUP(current)) { addIPartitions(c_term.symb(), p); }
            seen[id] = true;
        }
    }
}

ipartitions_t PartitionManager::computeAllowedPartitions(PTRef p) {
    vec<PTRef> vars = variables(logic, p);
    if (vars.size() == 0) { return 0; }
    ipartitions_t allowed = getIPartitions(vars[0]);
    for (int i = 1; i < vars.size(); ++i) {
        allowed &= getIPartitions(vars[i]);
    }
    return allowed;
}

namespace {
    bool isAlocal(ipartitions_t const & p, ipartitions_t const & mask) {
        return (p & mask) != 0;
    }
    bool isBlocal(ipartitions_t const & p, ipartitions_t const & mask) {
        return (p & ~mask) != 0;
    }
    bool isLocalTo(PartitionManager::part p, ipartitions_t const & p_mask, ipartitions_t const & mask) {
        return p == PartitionManager::part::A ? isAlocal(p_mask, mask) : isBlocal(p_mask, mask);
    }

    bool hasNoPartition(ipartitions_t const & p_mask, ipartitions_t const & mask) {
        return !isAlocal(p_mask, mask) and !isBlocal(p_mask, mask);
    }
} // namespace

PTRef PartitionManager::getPartition(ipartitions_t const & mask, PartitionManager::part p) {
    auto parts = getPartitions();
    vec<PTRef> args;
    for (auto part : parts) {
        int partitionIndex = getPartitionIndex(part);
        if (partitionIndex < 0) { throw InternalException("Internal error in partition bookkeeping"); }
        ipartitions_t p_mask = 0;
        setbit(p_mask, static_cast<unsigned>(partitionIndex));
        if (isLocalTo(p, p_mask, mask)) {
            args.push(part);
        } else if (hasNoPartition(p_mask, mask)) {
            throw InternalException("Assertion is neither A or B");
        }
    }
    PTRef requestedPartition = logic.mkAnd(std::move(args));
    return requestedPartition;
}

vec<PTRef> PartitionManager::getPartitions(ipartitions_t const & mask) const {
    vec<PTRef> res;
    for (PTRef topLevelPartition : getPartitions()) {
        int index = getPartitionIndex(topLevelPartition);
        assert(index >= 0);
        if (tstbit(mask, static_cast<unsigned>(index))) { res.push(topLevelPartition); }
    }
    return res;
}

void PartitionManager::addClauseClassMask(CRef c, ipartitions_t const & toadd) {
    partitionInfo.addClausePartition(c, toadd);
}

void PartitionManager::invalidatePartitions(ipartitions_t const & toinvalidate) {
    partitionInfo.invalidatePartitions(toinvalidate);
}
} // namespace opensmt
