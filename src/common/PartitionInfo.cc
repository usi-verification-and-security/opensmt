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

ipartitions_t & PartitionInfo::getVarPartition(Var v) {
    return var_class[v];
}

void PartitionInfo::addVarPartition(Var v, const ipartitions_t & p) {
    var_class[v] |= p;
}

void
PartitionInfo::invalidatePartitions(const ipartitions_t& toinvalidate) {
    auto negated = ~toinvalidate;
    for (auto & clause_info : clause_class) {
        auto& current_info = clause_info.second;
        opensmt::andbit(current_info, current_info, negated);
    }
    for (auto & var_info : var_class) {
        auto& current_info = var_info.second;
        opensmt::andbit(current_info, current_info, negated);
    }
    for (auto & term_info : term_partitions) {
        auto& current_info = term_info.second;
        opensmt::andbit(current_info, current_info, negated);
    }
    for (auto & sym_info : sym_partitions) {
        auto& current_info = sym_info.second;
        opensmt::andbit(current_info, current_info, negated);
    }
}