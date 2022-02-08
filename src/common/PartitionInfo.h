//
// Created by Martin Blicha on 2019-08-14.
//

#ifndef OPENSMT_PARTITIONINFO_H
#define OPENSMT_PARTITIONINFO_H

#include <unordered_map>

#include "InterpolationUtils.h"
#include "PTRef.h"
#include "SymRef.h"
#include "SolverTypes.h"
#include "FlaPartitionMap.h"


class PartitionInfo {
    std::unordered_map<SymRef, ipartitions_t, SymRefHash> sym_partitions;
    std::unordered_map<PTRef, ipartitions_t, PTRefHash> term_partitions;
    std::unordered_map<CRef, ipartitions_t> clause_class;
    FlaPartitionMap flaPartitionMap;

public:
    void assignTopLevelPartitionIndex(unsigned int n, PTRef tr); // The new partition system
    ipartitions_t& getIPartitions(PTRef t);
    void addIPartitions(PTRef t, const ipartitions_t& p);
    ipartitions_t& getIPartitions(SymRef _s);
    void addIPartitions(SymRef s, const ipartitions_t& p);
    const ipartitions_t& getClausePartitions(CRef) const;
    void addClausePartition(CRef c, const ipartitions_t& p);

    inline std::vector<PTRef> getTopLevelFormulas() const { return flaPartitionMap.get_top_level_flas(); }
    inline unsigned int getNoOfPartitions() const {return flaPartitionMap.getNoOfPartitions(); }
    inline void transferPartitionMembership(PTRef o, PTRef n) { return flaPartitionMap.transferPartitionMembership(o, n); }
    inline int getPartitionIndex(PTRef p) const { return flaPartitionMap.getPartitionIndex(p); }

    void invalidatePartitions(ipartitions_t const & p);
};

#endif //OPENSMT_PARTITIONINFO_H
