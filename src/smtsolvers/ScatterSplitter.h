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
#include "Splitter.h"

class ScatterSplitter : public SimpSMTSolver, virtual public Splitter {

public:
    ScatterSplitter(SMTConfig & c, THandler & t);

protected:
    std::vector<vec<Lit>> split_assumptions;
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
};


#endif //OPENSMT_SCATTERSPLITTER_H
