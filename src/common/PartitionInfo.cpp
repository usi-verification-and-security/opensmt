//
// Created by Martin Blicha on 2019-08-14.
//
#ifdef PRODUCE_PROOF
#include "PartitionInfo.h"

#ifdef PRODUCE_PROOF
void
PartitionInfo::assignPartition(unsigned int n, PTRef ptr) {
    assert(n >= 0);
    ipartitions_t p = 0;
    setbit(p, n);
    addIPartitions(ptr, p);
}

ipartitions_t&
PartitionInfo::getIPartitions(PTRef _t)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return term_partitions[_t];
}

void
PartitionInfo::setIPartitions(PTRef _t, const ipartitions_t& _p)
{
    term_partitions[_t] = _p;
}

void
PartitionInfo::addIPartitions(PTRef _t, const ipartitions_t& _p)
{
    term_partitions[_t] |= _p;
}

ipartitions_t&
PartitionInfo::getIPartitions(SymRef _s)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return sym_partitions[_s];
}

void
PartitionInfo::setIPartitions(SymRef _s, const ipartitions_t& _p)
{
    sym_partitions[_s] = _p;
}

void
PartitionInfo::addIPartitions(SymRef _s, const ipartitions_t& _p)
{
    sym_partitions[_s] |= _p;
}

#endif

#endif // PRODUCE_PROOF