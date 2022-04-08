/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_SCATTERSPLITTER_H
#define OPENSMT_SCATTERSPLITTER_H

#include "SimpSMTSolver.h"
#include "SplitData.h"
#include "SplitContext.h"

#include <PTPLib/net/Channel.hpp>
#include <PTPLib/common/Exception.hpp>

class ScatterSplitter : public SimpSMTSolver {
public:
    ScatterSplitter(SMTConfig & c, THandler & t, PTPLib::net::Channel & ch);

    std::vector<SplitData> const & getSplits() { return splitContext.getSplits(); }

    vec<opensmt::pair<int,int>> const &  get_solver_branch()  const  { return solverBranch; }

    void set_solver_branch(std::string solver_branch);

private:
    std::vector<vec<Lit>>   split_assumptions;
    SplitContext            splitContext;
    PTPLib::net::Channel &  channel;
    int                     trail_sent;
    bool                    firstPropagation;
    int                     numTriviallyPropagatedOnDl0;
    vec<opensmt::pair<int,int>> solverBranch;

    bool     scatterLevel();                                                  // Are we currently on a scatter level.
    opensmt::pair<SplitData,lbool> createSplitAndBlockAssumptions();          // Create a split formula and place it to the splits vector.
    bool     excludeAssumptions(vec<Lit> const & neg_constrs);                // Add a clause to the database and propagate

    void shallLearnClauses () override ;                                      // Check if solver is in clause share mode

protected:
    lbool solve_() override;
    bool branchLitRandom() override;
    Var doActivityDecision() override;
    bool okContinue() const override;
    ConsistencyAction notifyConsistency() override;
    void notifyEnd() override;
    lbool zeroLevelConflictHandler() override;                                // Common handling of zero-level conflict as it can happen at multiple places

    bool learnSomeClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas);

    inline bool isAssumptionVar(Var  v)   const &   { return theory_handler.getTMap().isAssumptionVar(v); }

    inline vec<opensmt::pair<int,int>> const & get_solverBranch(Var v) const {
        return theory_handler.getTMap().get_solverBranch(theory_handler.getTMap().get_FrameId(v));
    }

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


#endif //OPENSMT_SCATTERSPLITTER_H
