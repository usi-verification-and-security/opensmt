/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "Splitter.h"


void Splitter::set_solver_branch(std::string & solver_branch)
{
    solverBranch.clear();
    solver_branch.erase(std::remove(solver_branch.begin(), solver_branch.end(), ' '), solver_branch.end());
    std::string const delimiter = "," ;
    size_t beg, pos = 0;
    uint16_t counter = 0;
    uint16_t temp = 0;
    while ((beg = solver_branch.find_first_not_of(delimiter, pos)) != std::string::npos)
    {
        pos = solver_branch.find_first_of(delimiter, beg + 1);
        int index = stoi(solver_branch.substr(beg, pos - beg));
        if (counter % 2 == 1) {
            solverBranch.push({temp, index});
        } else temp = index;
        counter++;
    }
}

void Splitter::addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const> && solver_branch, uint32_t fid) {
    vec<opensmt::pair<int,int>> addrVector;
    addrVector.capacity(solver_branch.size());
    for (auto el : solver_branch) {
        addrVector.push(el);
    }
    mapSolverBranchToFrameId(fid, std::move(addrVector));
}

vec<opensmt::pair<int,int>> const & Splitter::getSolverBranch(Var v) {
    return frameIdToSolverBranch[get_FrameId(v)];
}

void Splitter::mapSolverBranchToFrameId(uint32_t fid, vec<opensmt::pair<int,int>> && solverAddress) {
    frameIdToSolverBranch[fid] = std::move(solverAddress);
}