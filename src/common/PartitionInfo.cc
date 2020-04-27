//
// Created by Martin Blicha on 2019-08-14.
//
#include "PartitionInfo.h"

void
PartitionInfo::assignTopLevelPartitionIndex(unsigned int n, PTRef tr) {
    assert(n >= 0);
    flaPartitionMap.store_top_level_fla_index(tr, n);
    ipartitions_t p = 0;
    setbit(p, n);
    addIPartitions(tr, p);
}

ipartitions_t&
PartitionInfo::getIPartitions(PTRef _t)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return term_partitions[_t];
}

void
PartitionInfo::addIPartitions(PTRef _t, const ipartitions_t& _p)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    term_partitions[_t] |= _p;
}

ipartitions_t&
PartitionInfo::getIPartitions(SymRef _s)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return sym_partitions[_s];
}

void
PartitionInfo::addIPartitions(SymRef _s, const ipartitions_t& _p)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    sym_partitions[_s] |= _p;
}

ipartitions_t & PartitionInfo::getClausePartitions(CRef c) {
    return clause_class[c];
}

void PartitionInfo::addClausePartition(CRef c, const ipartitions_t & p) {
    //opensmt::orbit(clause_class[c], clause_class[c], p);
    clause_class[c] |= p;
}

void
PartitionInfo::invalidatePartitions(const ipartitions_t& toinvalidate) {
    auto negated = ~toinvalidate;
    for (auto it = term_partitions.begin(); it != term_partitions.end(); /* deliberately empty */) {
        auto& current_info = it->second;
        opensmt::andbit(current_info, current_info, negated);
        if (current_info == 0) {
            it = term_partitions.erase(it);
        }
        else {
            ++it;
        }
    }
    for (auto & sym_info : sym_partitions) {
        auto& current_info = sym_info.second;
        opensmt::andbit(current_info, current_info, negated);
    }
}