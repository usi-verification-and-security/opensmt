//
// Created by Martin Blicha on 06.10.18.
//

#ifndef OPENSMT_FLAPARTITIONMAP_H
#define OPENSMT_FLAPARTITIONMAP_H

#include "PTRef.h"

#include <map>
#include <vector>

struct PartIdx {
    int id;
    bool operator== (const PartIdx o) const { return o.id == id; }
    bool operator!= (const PartIdx o) const { return o.id != id; }
};
const struct PartIdx PartIdx_Default = {0};
const struct PartIdx PartIdx_Undef   = {INT32_MAX};

class FlaPartitionMap {
    std::map<PTRef, unsigned int> top_level_flas;
    std::map<PTRef, unsigned int> other_flas;

public:
    void store_top_level_fla_index(PTRef fla, unsigned int idx) { top_level_flas[fla] = idx; }
    void store_other_fla_index(PTRef fla, unsigned int idx) { other_flas[fla] = idx; }
    std::vector<PTRef> get_top_level_flas () const;
    unsigned getNoOfPartitions() const {return get_top_level_flas().size();}
    void transferPartitionMembership(PTRef old, PTRef new_ptref);
    PartIdx getPartitionIndex(PTRef ref) const;
};


#endif //OPENSMT_FLAPARTITIONMAP_H
