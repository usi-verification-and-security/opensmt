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
    PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> &  channel;
    using map_frameId_solverBranch = std::map<uint32_t, vec<opensmt::pair<int,int>>>;
    map_frameId_solverBranch frameIdToSolverBranch;
    using map_var_frameId = std::map<Var ,uint32_t>;
    map_var_frameId varToFrameId;

public:
    Splitter(SMTConfig & c, PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & ch)
    : splitContext(c)
    , channel(ch)
    {}

    std::vector<SplitData>      const & getSplits() const { return splitContext.getSplits(); }

    bool isSplitTypeScatter()   const  { return splitContext.isSplitTypeScatter(); }

    bool isSplitTypeLookahead()  const { return splitContext.isSplitTypeLookahead(); }

    bool isSplitTypeNone()       const { return splitContext.isSplitTypeNone(); }

    void resetSplitType()              { splitContext.resetSplitType(); }

    PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & getChannel() const   { return channel; }

    inline void setSolverBranch(vec<opensmt::pair<int,int>> && vec) { solverBranch = std::move(vec); }

    void addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const> && solver_branch, uint32_t fid);

    void mapSolverBranchToFrameId(uint32_t fid, vec<opensmt::pair<int,int>> && solverAddress);

    vec<opensmt::pair<int,int>> const &  getSolverBranch()  const  { return solverBranch; }

};

#endif //PARALLEL_SPLITTER_H
