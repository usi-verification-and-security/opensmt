/*
 *  Copyright (c) 2018, Martin Blicha <martin.blicha@gmail.com>
 *                2025, Tomas Kolarik <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "FlaPartitionMap.h"

namespace opensmt {
std::vector<PTRef> FlaPartitionMap::getTopLevelFlas() const {
    std::vector<PTRef> res;
    res.reserve(topLevelFlaToIdxMap.size());
    for (auto entry : topLevelFlaToIdxMap) {
        res.push_back(entry.first);
    }
    return res;
}

std::vector<PTRef> FlaPartitionMap::getInternalFlas() const {
    std::vector<PTRef> res;
    res.reserve(topLevelFlaToIdxMap.size());
    for (auto entry : topLevelFlaToIdxMap) {
        res.push_back(entry.first);
    }
    return res;
}

void FlaPartitionMap::transferPartitionMembership(PTRef old, PTRef new_ptref) {
    if (auto it = internalFlaToIdxMap.find(old); it != internalFlaToIdxMap.end()) {
        unsigned int const idx = it->second;
        storeInternalFlaIndex(new_ptref, idx);
        internalFlaToIdxMap.erase(it);
        assert(internalIdxToFlaMap.contains(idx) and internalIdxToFlaMap.at(idx) == new_ptref);
        return;
    }

    if (auto it = topLevelFlaToIdxMap.find(old); it != topLevelFlaToIdxMap.end()) {
        storeInternalFlaIndex(new_ptref, it->second);
    }
}

int FlaPartitionMap::getPartitionIndex(PTRef ref) const {
    if (auto it = topLevelFlaToIdxMap.find(ref); it != topLevelFlaToIdxMap.end()) {
        return static_cast<int>(it->second);
    }
    if (auto it = internalFlaToIdxMap.find(ref); it != internalFlaToIdxMap.end()) {
        return static_cast<int>(it->second);
    }
    return -1;
}
} // namespace opensmt
