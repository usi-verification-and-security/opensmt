/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef OPENSMT_PARALLELSCATTERSPLITTER_H
#define OPENSMT_PARALLELSCATTERSPLITTER_H

#include "ScatterSplitter.h"

#include <PTPLib/net/Channel.hpp>
#include <PTPLib/common/Exception.hpp>
#include <PTPLib/common/Printer.hpp>

class ParallelScatterSplitter : public ScatterSplitter  {
public:
    ParallelScatterSplitter(SMTConfig & c, THandler & t);
    void set_channel(PTPLib::net::Channel & ch) { channel = &ch; }   //SMTS Client owns the channel and should directly set the channel in ParallelScatterSpitter
    PTPLib::net::Channel & getChannel() const   { return *channel; }
    void set_syncedStream(PTPLib::common::synced_stream & ss) { syncedStream = &ss; }  //SMTS Client owns the SyncedStream and should directly set the SyncedStream in ParallelScatterSpitter
    vec<opensmt::pair<int,int>> const &  get_solver_branch()  const  { return solverBranch; }
    void set_solver_branch(std::string solver_branch);
    void mapSolverBranchToFrameId(uint32_t fid, vec<opensmt::pair<int,int>> && solverAddress) {
        frameId_solverBranch[fid] = std::move(solverAddress);
    }
    void addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const> && solver_branch, uint32_t fid);

    inline vec<opensmt::pair<int,int>> const & get_solverBranch(Var v) { return frameId_solverBranch[theory_handler.getTMap().get_FrameId(v)]; }

private:
    PTPLib::net::Channel *  channel;
    int                     trail_sent;
    bool                    firstPropagation;
    int                     numTriviallyPropagatedOnDl0;

    vec<opensmt::pair<int,int>> solverBranch;
    PTPLib::common::synced_stream * syncedStream;
    using map_frameId_solverBranch = std::map<uint32_t, vec<opensmt::pair<int,int>>>;
    map_frameId_solverBranch frameId_solverBranch;
    using map_var_frameId = std::map<Var ,uint32_t>;
    map_var_frameId var_frameId;

    void runPeriodic() override;                                       // Check if solver is in clause share mode to starts clause exposing operation

    void notifyResult(lbool const & result) const;                     // OpenSMT signalling to communication channel that it's found a result and will stop

protected:

    lbool solve_() override;
    bool okContinue() const override;
    ConsistencyAction notifyConsistency() override;
    void notifyEnd() override;
    lbool zeroLevelConflictHandler() override;                                // Common handling of zero-level conflict as it can happen at multiple places

    bool exposeClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas);

    int getAssumptionLevel(Var v) const;

    inline bool isPrefix(const vec<opensmt::pair<int,int>> &  prefix, const vec<opensmt::pair<int,int>> &  full)
    {
        if (prefix.size() > full.size())
            return false;
        for (int i = 0; i < prefix.size(); ++i) {
            if (prefix[i].first != full[i].first or prefix[i].second != full[i].second)
                return false;
        }
        return true;
    }
};


#endif //OPENSMT_PARALLELSCATTERSPLITTER_H