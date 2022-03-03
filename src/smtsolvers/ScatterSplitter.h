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
#include "SplitConfig.h"

class ScatterSplitter : public SimpSMTSolver {
public:
    ScatterSplitter(SMTConfig & c, THandler & t);
    void setSplitConfig_split_on()                                    { splitConfig.split_on = true; };
    bool                      const &    getSplitConfig_split_on()    { return splitConfig.split_on; }
    std::vector<SplitData>    const &    getSplits()                  { return splits; }
private:
    std::vector<vec<Lit>> split_assumptions;
    std::vector<SplitData> splits;
    SplitConfig splitConfig;
    void     updateSplitState();                                                       // Update the state of the splitting machine.
    bool     scatterLevel();                                                           // Are we currently on a scatter level.
    bool     createSplit_scatter();                                                    // Create a split formula and place it to the splits vector.
    bool     excludeAssumptions(vec<Lit>& neg_constrs);                                // Add a clause to the database and propagate
protected:
    virtual lbool solve_() override;
    virtual inline void clausesPublish() {};
    virtual inline void clausesUpdate() {};
    bool branchLitRandom() override;
    Var doActivityDecision() override;
    bool okContinue() const override;
    void runPeriodics();                // Update clauses
    virtual lbool search(int nof_conflicts, int nof_learnts) override;                  // Search for a given number of conflicts.
    virtual lbool zeroLevelConflictHandler() override;                                  // Common handling of zero-level conflict as it can happen at multiple places
};


#endif //OPENSMT_SCATTERSPLITTER_H
