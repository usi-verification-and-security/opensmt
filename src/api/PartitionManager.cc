/*
 *  Copyright (c) 2020 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "PartitionManager.h"
#include "TreeOps.h"
#include "OsmtInternalException.h"

void PartitionManager::propagatePartitionMask(PTRef root) {
    ipartitions_t& p = getIPartitions(root);
    std::vector<bool> seen;
    // MB: Relies on invariant: Every subterm was created before its parent, so it has lower id
    auto size = Idx(logic.getPterm(root).getId()) + 1;
    seen.resize(size, false);
    std::vector<PTRef> queue {root};
    while (!queue.empty()) {
        PTRef current = queue.back();
        queue.pop_back();
        const Pterm& c_term = logic.getPterm(current);
        auto id = Idx(c_term.getId());
        assert(id < size);
        if (!seen[id]) {
            addIPartitions(current, p);
            for (int j = 0; j < c_term.size(); ++j) {
                queue.push_back(c_term[j]);
            }
            if (logic.isUF(current) || logic.isUP(current)) {
                addIPartitions(c_term.symb(), p);
            }
            seen[id] = true;
        }
    }
}

ipartitions_t PartitionManager::computeAllowedPartitions(PTRef p) {
    vec<PtChild> subterms;
    getTermList(p, subterms, logic);
    vec<PTRef> vars;
    for (int i = 0; i < subterms.size(); ++i) {
        if (logic.isVar(subterms[i].tr)) {
            vars.push(subterms[i].tr);
        }
    }
    if (vars.size() == 0) { return 0; }
    ipartitions_t allowed = getIPartitions(vars[0]);
    for (int i = 1; i < vars.size(); ++i) {
        allowed &= getIPartitions(vars[i]);
    }
    return allowed;
}

using opensmt::isAlocal;
using opensmt::isBlocal;

PTRef PartitionManager::getPartition(const ipartitions_t& mask, PartitionManager::part p)
{
    auto isLocalToP = [p](const ipartitions_t& p_mask, const ipartitions_t& mask){ return p == part::A ? isAlocal(p_mask, mask) : isBlocal(p_mask, mask); };
    auto hasNoPartition = [](const ipartitions_t& p_mask, const ipartitions_t&mask) { return !isAlocal(p_mask, mask) and !isBlocal(p_mask, mask); };
    auto parts = getPartitions();
    vec<PTRef> args;
    for (auto part : parts)
    {
        int partitionIndex = getPartitionIndex(part);
        if (partitionIndex < 0) {
            throw OsmtInternalException("Internal error in partition bookkeeping");
        }
        ipartitions_t p_mask = 0;
        opensmt::setbit(p_mask, static_cast<unsigned>(partitionIndex));
        if (isLocalToP(p_mask, mask)) {
            args.push(part);
        }
        else if (hasNoPartition(p_mask, mask)) {
            throw OsmtInternalException("Assertion is neither A or B");
        }
    }
    PTRef requestedPartition = logic.mkAnd(std::move(args));
    return requestedPartition;
}

void
PartitionManager::addClauseClassMask(CRef c, const ipartitions_t& toadd)
{
    partitionInfo.addClausePartition(c, toadd);
}

void
PartitionManager::invalidatePartitions(const ipartitions_t& toinvalidate) {
    partitionInfo.invalidatePartitions(toinvalidate);
}
