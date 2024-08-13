//
// Created by Martin Blicha on 2019-08-14.
//

#include "PartitionInfo.h"

namespace opensmt {
void PartitionInfo::assignTopLevelPartitionIndex(unsigned int n, PTRef tr) {
    flaPartitionMap.store_top_level_fla_index(tr, n);
    ipartitions_t p = 0;
    setbit(p, n);
    addIPartitions(tr, p);
}

ipartitions_t & PartitionInfo::getIPartitions(PTRef _t) {
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return term_partitions[_t];
}

void PartitionInfo::addIPartitions(PTRef _t, ipartitions_t const & _p) {
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    term_partitions[_t] |= _p;
}

ipartitions_t & PartitionInfo::getIPartitions(SymRef _s) {
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return sym_partitions[_s];
}

void PartitionInfo::addIPartitions(SymRef _s, ipartitions_t const & _p) {
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    sym_partitions[_s] |= _p;
}

ipartitions_t const & PartitionInfo::getClausePartitions(CRef c) const {
    return clause_class.at(c);
}

void PartitionInfo::addClausePartition(CRef c, ipartitions_t const & p) {
    //    orbit(clause_class[c], clause_class[c], p);
    clause_class[c] |= p;
}

void PartitionInfo::invalidatePartitions(ipartitions_t const & toinvalidate) {
    auto negated = ~toinvalidate;
    for (auto it = term_partitions.begin(); it != term_partitions.end(); /* deliberately empty */) {
        auto & current_info = it->second;
        andbit(current_info, current_info, negated);
        if (current_info == 0) {
            it = term_partitions.erase(it);
        } else {
            ++it;
        }
    }
    for (auto & sym_info : sym_partitions) {
        auto & current_info = sym_info.second;
        andbit(current_info, current_info, negated);
    }
}
} // namespace opensmt
