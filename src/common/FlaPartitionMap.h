/*
 *  Copyright (c) 2018, Martin Blicha <martin.blicha@gmail.com>
 *                2025, Tomas Kolarik <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_FLAPARTITIONMAP_H
#define OPENSMT_FLAPARTITIONMAP_H

#include <pterms/PTRef.h>

#include <cassert>
#include <map>
#include <unordered_map>
#include <vector>

namespace opensmt {
class FlaPartitionMap {
public:
    inline void storeTopLevelFlaIndex(PTRef fla, unsigned int idx);
    inline void storeInternalFlaIndex(PTRef fla, unsigned int idx);
    std::vector<PTRef> getTopLevelFlas() const;
    std::vector<PTRef> getInternalFlas() const;
    inline PTRef getTopLevelFla(unsigned int idx) const noexcept;
    inline PTRef getInternalFla(unsigned int idx) const noexcept;
    inline unsigned getNoOfPartitions() const;
    void transferPartitionMembership(PTRef old, PTRef new_ptref);
    int getPartitionIndex(PTRef ref) const;

private:
    std::map<PTRef, unsigned int> topLevelFlaToIdxMap;
    std::map<PTRef, unsigned int> internalFlaToIdxMap;
    std::unordered_map<unsigned int, PTRef> topLevelIdxToFlaMap;
    std::unordered_map<unsigned int, PTRef> internalIdxToFlaMap;
};

void FlaPartitionMap::storeTopLevelFlaIndex(PTRef fla, unsigned int idx) {
    topLevelFlaToIdxMap[fla] = idx;
    topLevelIdxToFlaMap[idx] = fla;
}

void FlaPartitionMap::storeInternalFlaIndex(PTRef fla, unsigned int idx) {
    internalFlaToIdxMap[fla] = idx;
    internalIdxToFlaMap[idx] = fla;
}

PTRef FlaPartitionMap::getTopLevelFla(unsigned int idx) const noexcept {
    if (auto it = topLevelIdxToFlaMap.find(idx); it != topLevelIdxToFlaMap.end()) { return it->second; }
    return PTRef_Undef;
}

PTRef FlaPartitionMap::getInternalFla(unsigned int idx) const noexcept {
    if (auto it = internalIdxToFlaMap.find(idx); it != internalIdxToFlaMap.end()) { return it->second; }
    return PTRef_Undef;
}

unsigned FlaPartitionMap::getNoOfPartitions() const {
    assert(getTopLevelFlas().size() == topLevelFlaToIdxMap.size());
    assert(topLevelFlaToIdxMap.size() <= topLevelIdxToFlaMap.size());
    return topLevelFlaToIdxMap.size();
}

} // namespace opensmt

#endif // OPENSMT_FLAPARTITIONMAP_H
