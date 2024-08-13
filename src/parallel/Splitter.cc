/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Splitter.h"

namespace opensmt::parallel {

void Splitter::addBranchToFrameId(span<pair<int, int> const> && solver_branch, uint32_t fid) {
    vec<pair<int,int>> addrVector;
    addrVector.capacity(solver_branch.size());
    for (auto el : solver_branch) {
        addrVector.push(el);
    }
    mapSolverBranchToFrameId(fid, std::move(addrVector));
}

void Splitter::mapSolverBranchToFrameId(uint32_t fid, vec<pair<int,int>> && solverAddress) {
    frameIdToSolverBranch[fid] = std::move(solverAddress);
}

}
