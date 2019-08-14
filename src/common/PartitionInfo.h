//
// Created by Martin Blicha on 2019-08-14.
//

#ifndef OPENSMT_PARTITIONINFO_H
#define OPENSMT_PARTITIONINFO_H

#ifdef PRODUCE_PROOF

#include <unordered_map>

#include "PTRef.h"
#include "SymRef.h"
#include "Global.h" // TODO: move the definition of ipartitions_t here


class PartitionInfo {
    std::unordered_map<SymRef, ipartitions_t, SymRefHash> sym_partitions;
    std::unordered_map<PTRef, ipartitions_t, PTRefHash> term_partitions;

public:
    void assignPartition(unsigned int n, PTRef tr); // The new partition system
    ipartitions_t& getIPartitions(PTRef _t);
    void setIPartitions(PTRef _t, const ipartitions_t& _p);
    void addIPartitions(PTRef _t, const ipartitions_t& _p);
    ipartitions_t& getIPartitions(SymRef _s);
    void setIPartitions(SymRef _s, const ipartitions_t& _p);
    void addIPartitions(SymRef _s, const ipartitions_t& _p);
};

#endif //PRODUCE_PROOF

#endif //OPENSMT_PARTITIONINFO_H
