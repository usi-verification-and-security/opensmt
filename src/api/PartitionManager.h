//
// Created by prova on 05.08.20.
//

#ifndef OPENSMT_PARTITIONMANAGER_H
#define OPENSMT_PARTITIONMANAGER_H

#include "Logic.h"

class PartitionManager {
    PartitionInfo partitionInfo;
    Logic &logic;

public:
    PartitionManager(Logic& l) : logic(l) {
        // MB: TODO: Is this necessary?
        ipartitions_t mask = 0; mask = ~mask;  addIPartitions(logic.getTerm_true(), mask); addIPartitions(logic.getTerm_false(), mask);
    }

    PTRef getPartitionA(const ipartitions_t&);
    PTRef getPartitionB(const ipartitions_t&);

    //partitions:
    ipartitions_t& getIPartitions(PTRef _t) { return partitionInfo.getIPartitions(_t); }
    void addIPartitions(PTRef _t, const ipartitions_t& _p) { partitionInfo.addIPartitions(_t, _p); }
    ipartitions_t& getIPartitions(SymRef _s) { return partitionInfo.getIPartitions(_s); }
    void addIPartitions(SymRef _s, const ipartitions_t& _p) { partitionInfo.addIPartitions(_s, _p); }
    void propagatePartitionMask(PTRef tr);
    void assignTopLevelPartitionIndex(unsigned int n, PTRef tr)
    {
        partitionInfo.assignTopLevelPartitionIndex(n, tr);
    }

    ipartitions_t  computeAllowedPartitions(PTRef p);
    const ipartitions_t& getClauseClassMask(CRef c) const { return partitionInfo.getClausePartitions(c); }
    void addClauseClassMask(CRef c, const ipartitions_t& toadd);
    void invalidatePartitions(const ipartitions_t& toinvalidate);
    inline std::vector<PTRef> getPartitions() { return partitionInfo.getTopLevelFormulas(); }


    std::vector<PTRef> getPartitions(ipartitions_t const & mask){
        throw std::logic_error{"Not supported at the moment!"};
    }

    unsigned getNofPartitions() { return partitionInfo.getNoOfPartitions(); }

    void transferPartitionMembership(PTRef old, PTRef new_ptref)
    {
        this->addIPartitions(new_ptref, getIPartitions(old));
        partitionInfo.transferPartitionMembership(old, new_ptref);
    }

    int getPartitionIndex(PTRef ref) const {
        return partitionInfo.getPartitionIndex(ref);
    }
};


#endif //OPENSMT_PARTITIONMANAGER_H
