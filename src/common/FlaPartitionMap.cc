//
// Created by Martin Blicha on 06.10.18.
//

#include "FlaPartitionMap.h"

namespace opensmt {
std::vector<PTRef> FlaPartitionMap::get_top_level_flas() const {
    std::vector<PTRef> res;
    res.reserve(top_level_flas.size());
    for (auto entry : top_level_flas) {
        res.push_back(entry.first);
    }
    return res;
}

void FlaPartitionMap::transferPartitionMembership(PTRef old, PTRef new_ptref) {
    auto it = top_level_flas.find(old);
    if (it != top_level_flas.end()) {
        store_other_fla_index(new_ptref, it->second);
        return;
    }
    auto other_it = other_flas.find(old);
    if (other_it != other_flas.end()) { store_other_fla_index(new_ptref, other_it->second); }
}

int FlaPartitionMap::getPartitionIndex(PTRef ref) const {
    auto it = top_level_flas.find(ref);
    if (it != top_level_flas.end()) { return static_cast<int>(it->second); }
    auto other_it = other_flas.find(ref);
    if (other_it != other_flas.end()) { return static_cast<int>(other_it->second); }
    return -1;
}
} // namespace opensmt
