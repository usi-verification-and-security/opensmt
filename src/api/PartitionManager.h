/*
 *  Copyright (c) 2020 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_PARTITIONMANAGER_H
#define OPENSMT_PARTITIONMANAGER_H

#include <common/PartitionInfo.h>
#include <logics/Logic.h>

namespace opensmt {
class PartitionManager {
public:
    PartitionManager(Logic & l) : logic(l) {
        // MB: TODO: Is this necessary?
        ipartitions_t mask = 0;
        mask = ~mask;
        addIPartitions(logic.getTerm_true(), mask);
        addIPartitions(logic.getTerm_false(), mask);
    }

    enum class part { A, B };

    PTRef getPartition(ipartitions_t const &, part);

    // partitions:
    ipartitions_t & getIPartitions(PTRef _t) { return partitionInfo.getIPartitions(_t); }

    void addIPartitions(PTRef _t, ipartitions_t const & _p) { partitionInfo.addIPartitions(_t, _p); }

    ipartitions_t & getIPartitions(SymRef _s) { return partitionInfo.getIPartitions(_s); }

    void addIPartitions(SymRef _s, ipartitions_t const & _p) { partitionInfo.addIPartitions(_s, _p); }

    void propagatePartitionMask(PTRef tr);

    void assignTopLevelPartitionIndex(unsigned int n, PTRef tr) { partitionInfo.assignTopLevelPartitionIndex(n, tr); }

    ipartitions_t computeAllowedPartitions(PTRef p);

    ipartitions_t const & getClauseClassMask(CRef c) const { return partitionInfo.getClausePartitions(c); }

    void addClauseClassMask(CRef c, ipartitions_t const & toadd);

    void invalidatePartitions(ipartitions_t const & toinvalidate);

    inline std::vector<PTRef> getPartitions() const { return partitionInfo.getTopLevelFormulas(); }

    vec<PTRef> getPartitions(ipartitions_t const &) const;

    unsigned getNofPartitions() const { return partitionInfo.getNoOfPartitions(); }

    void transferPartitionMembership(PTRef old, PTRef new_ptref) {
        if (new_ptref == old) { return; }
        this->addIPartitions(new_ptref, getIPartitions(old));
        partitionInfo.transferPartitionMembership(old, new_ptref);
    }

    int getPartitionIndex(PTRef ref) const { return partitionInfo.getPartitionIndex(ref); }

private:
    PartitionInfo partitionInfo;
    Logic & logic;
};

} // namespace opensmt

#endif // OPENSMT_PARTITIONMANAGER_H
