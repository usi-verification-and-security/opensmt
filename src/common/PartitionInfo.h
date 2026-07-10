/*
 *  Copyright (c) 2019-2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_PARTITIONINFO_H
#define OPENSMT_PARTITIONINFO_H

#include "FlaPartitionMap.h"
#include "Partitions.h"

#include <minisat/core/SolverTypes.h>
#include <pterms/PTRef.h>
#include <symbols/SymRef.h>

#include <unordered_map>

namespace opensmt {
class PartitionInfo {
public:
    void assignTopLevelPartitionIndex(unsigned int n, PTRef tr); // The new partition system
    ipartitions_t & getIPartitions(PTRef t);
    void addIPartitions(PTRef t, ipartitions_t const & p);
    ipartitions_t & getIPartitions(SymRef _s);
    void addIPartitions(SymRef s, ipartitions_t const & p);
    ipartitions_t const & getClausePartitions(CRef) const;
    void addClausePartition(CRef c, ipartitions_t const & p);

    inline std::vector<PTRef> getTopLevelFormulas() const { return flaPartitionMap.getTopLevelFlas(); }
    inline std::vector<PTRef> getInternalFormulas() const { return flaPartitionMap.getInternalFlas(); }
    inline PTRef getTopLevelFormula(unsigned int idx) const { return flaPartitionMap.getTopLevelFla(idx); }
    inline PTRef getInternalFormula(unsigned int idx) const { return flaPartitionMap.getInternalFla(idx); }
    inline unsigned int getNoOfPartitions() const { return flaPartitionMap.getNoOfPartitions(); }
    inline void transferPartitionMembership(PTRef o, PTRef n) {
        return flaPartitionMap.transferPartitionMembership(o, n);
    }
    inline int getPartitionIndex(PTRef p) const { return flaPartitionMap.getPartitionIndex(p); }

    void invalidatePartitions(ipartitions_t const & p);

private:
    std::unordered_map<SymRef, ipartitions_t, SymRefHash> sym_partitions;
    std::unordered_map<PTRef, ipartitions_t, PTRefHash> term_partitions;
    std::unordered_map<CRef, ipartitions_t> clause_class;
    FlaPartitionMap flaPartitionMap;
};
} // namespace opensmt

#endif // OPENSMT_PARTITIONINFO_H
