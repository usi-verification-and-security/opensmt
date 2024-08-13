/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */
#ifndef PARALLEL_SCATTERSPLITTER_H
#define PARALLEL_SCATTERSPLITTER_H

#include "SplitData.h"
#include "SplitContext.h"
#include "Splitter.h"

#include <smtsolvers/SimpSMTSolver.h>
#include <common/TreeOps.h>

#include <PTPLib/net/Channel.hpp>
#include <PTPLib/common/Exception.hpp>
#include <PTPLib/common/Printer.hpp>

namespace opensmt::parallel {

class ScatterSplitter :  public SimpSMTSolver, public Splitter {
public:
    ScatterSplitter(SMTConfig & c, THandler & t, PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & ch);

    void set_syncedStream(PTPLib::common::synced_stream & ss) { syncedStream = &ss; }  //SMTS Client owns the SyncedStream and should directly set the SyncedStream

    void enterSplittingCycle()          { splitContext.enterSplittingCycle(); }

    bool isSplitTypeNone()     const    { return splitContext.isSplitTypeNone(); }

    void resetSplitType()               { splitContext.resetSplitType(); }

    void setSplitTypeScatter()          { splitContext.setSplitTypeScatter(); }

    int getSplitTypeValue() const       { return splitContext.getSplitTypeValue(); }

    int getSearchCounter()  const       {  return search_counter; }

    void mapEnabledFrameIdToVar(Var v, uint32_t fid, uint32_t & prevId) override;

private:
    int                     trail_sent = 0;
    bool                    firstPropagation = true;
    int                     numTriviallyPropagatedOnDl0 = 0;

    using map_var_frameId = std::map<Var ,uint32_t>;
    map_var_frameId var_frameId;

    std::unordered_set<Var> assumptionVars;

    PTPLib::common::synced_stream * syncedStream = nullptr;

    PtermNodeCounter nodeCounter;

    void runPeriodic() override;                                       // Check if solver is in clause share mode to starts clause exposing operation

protected:
    bool     scatterLevel();                                                  // Are we currently on a scatter level.
    pair<SplitData,lbool> createSplitAndBlockAssumptions();          // Create a split formula and place it to the splits vector.
    bool     excludeAssumptions(vec<Lit> && neg_constrs);                     // Add a clause to the database and propagate
    bool isAssumptionVar(Var v) const { return assumptionVars.find(v) != assumptionVars.end(); }

    lbool solve_() override;
    bool branchLitRandom() override;
    Var doActivityDecision() override;
    bool okContinue() const override;
    ConsistencyAction notifyConsistency() override;
    void notifyEnd() override;
    lbool zeroLevelConflictHandler() override;                                // Common handling of zero-level conflict as it can happen at multiple places

    void exposeUnitClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas);
    void exposeLongerClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas);
    bool exposeClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas);

    bool isPrefix(const vec<pair<int,int>> &  prefix, const vec<pair<int,int>> &  full)
    {
        if (prefix.size() > full.size())
            return false;
        for (int i = 0; i < prefix.size(); ++i) {
            if (prefix[i].first != full[i].first or prefix[i].second != full[i].second)
                return false;
        }
        return true;
    }

    uint32_t get_FrameId(Var v) { return var_frameId[v]; }

    void addAssumptionVar(Var v) override { assumptionVars.insert(v); }

    vec<pair<int,int>> const & getBranchOfVar(Var v);
};

}

#endif //PARALLEL_SCATTERSPLITTER_H
