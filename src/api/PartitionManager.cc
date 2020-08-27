//
// Created by prova on 05.08.20.
//

#include "PartitionManager.h"
#include "TreeOps.h"

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

PTRef
PartitionManager::getPartitionA(const ipartitions_t& mask)
{
    auto parts = getPartitions();
    vec<PTRef> a_args;
    for (auto part : parts)
    {
        const auto & p_mask = getIPartitions(part);
        if (isAlocal(p_mask, mask)) {
            a_args.push(part);
        }
        else if (!isBlocal(p_mask, mask)) {
            opensmt_error("Assertion is neither A or B");
        }
    }

    PTRef A = logic.mkAnd(a_args);

    return A;
}

PTRef
PartitionManager::getPartitionB(const ipartitions_t& mask)
{
    auto parts = getPartitions();
    vec<PTRef> b_args;
    for (auto part : parts)
    {
        const auto & p_mask = getIPartitions(part);
        if (isBlocal(p_mask, mask)) {
            b_args.push(part);
        }
        else if (!isAlocal(p_mask, mask)) {
            opensmt_error("Assertion is neither A or B");
        }
    }

    PTRef B = logic.mkAnd(b_args);
    return B;
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
