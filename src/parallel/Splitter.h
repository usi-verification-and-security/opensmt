/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_SPLITTER_H
#define PARALLEL_SPLITTER_H

#include "SplitData.h"
#include "SplitContext.h"

#include <PTPLib/net/Channel.hpp>

class Splitter {

private:
    vec<opensmt::pair<int,int>> solverBranch;

protected:
    SplitContext splitContext;
    PTPLib::net::Channel &  channel;

public:
    Splitter(SMTConfig & c, PTPLib::net::Channel & ch)
    : splitContext(c)
    , channel(ch)
    {}

    std::vector<SplitData>      const & getSplits() { return splitContext.getSplits(); }

    bool isSplitTypeScatter()   const  { return splitContext.isSplitTypeScatter(); }

    bool isSplitTypeLookahead()  const { return splitContext.isSplitTypeLookahead(); }

    bool isSplitTypeNone()       const { return splitContext.isSplitTypeNone(); }

    void resetSplitType() { splitContext.resetSplitType(); }

    vec<opensmt::pair<int,int>> const &  get_solver_branch()  const  { return solverBranch; }

    PTPLib::net::Channel & getChannel() const   { return channel; }

    void set_solver_branch(std::string & solver_branch)
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
};

#endif //PARALLEL_SPLITTER_H
