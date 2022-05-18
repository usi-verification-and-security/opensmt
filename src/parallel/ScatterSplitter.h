/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef PARALLEL_SCATTERSPLITTER_H
#define PARALLEL_SCATTERSPLITTER_H

#include "SimpSMTSolver.h"
#include "SplitData.h"
#include "SplitContext.h"
#include "Splitter.h"

#include <PTPLib/net/Channel.hpp>
#include <PTPLib/common/Exception.hpp>
#include <PTPLib/common/Printer.hpp>

class ScatterSplitter :  public SimpSMTSolver, public Splitter {
public:
    ScatterSplitter(SMTConfig & c, THandler & t, PTPLib::net::Channel & ch);

    void set_syncedStream(PTPLib::common::synced_stream & ss) { syncedStream = &ss; }  //SMTS Client owns the SyncedStream and should directly set the SyncedStream

    void mapSolverBranchToFrameId(uint32_t fid, vec<opensmt::pair<int,int>> && solverAddress) {
        frameIdToSolverBranch[fid] = std::move(solverAddress);
    }
    void addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const> && solver_branch, uint32_t fid);

    inline vec<opensmt::pair<int,int>> const & getSolverBranch(Var v) { return frameIdToSolverBranch[theory_handler.getTMap().get_FrameId(v)]; }

    void enterSplittingCycle()          { splitContext.enterSplittingCycle(); }

    bool isSplitTypeNone()     const    { return splitContext.isSplitTypeNone(); }

    void resetSplitType()               { splitContext.resetSplitType(); }

    void setSplitTypeScatter()          { splitContext.setSplitTypeScatter(); }

    int getSplitTypeValue() const       { return splitContext.getSplitTypeValue(); }


private:
    int                     trail_sent = 0;
    bool                    firstPropagation = true;
    int                     numTriviallyPropagatedOnDl0;

    PTPLib::common::synced_stream * syncedStream = nullptr;
    using map_frameId_solverBranch = std::map<uint32_t, vec<opensmt::pair<int,int>>>;
    map_frameId_solverBranch frameIdToSolverBranch;
    using map_var_frameId = std::map<Var ,uint32_t>;
    map_var_frameId var_frameId;

    void runPeriodic() override;                                       // Check if solver is in clause share mode to starts clause exposing operation

protected:
    bool     scatterLevel();                                                  // Are we currently on a scatter level.
    opensmt::pair<SplitData,lbool> createSplitAndBlockAssumptions();          // Create a split formula and place it to the splits vector.
    bool     excludeAssumptions(vec<Lit> const & neg_constrs);                // Add a clause to the database and propagate
    inline bool isAssumptionVar(Var  v)   const &   { return theory_handler.getTMap().isAssumptionVar(v); }

    lbool solve_() override;
    bool branchLitRandom() override;
    Var doActivityDecision() override;
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


#endif //PARALLEL_SCATTERSPLITTER_H