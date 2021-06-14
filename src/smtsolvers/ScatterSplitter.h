//
// Created by prova on 31.03.21.
//

#ifndef OPENSMT_SCATTERSPLITTER_H
#define OPENSMT_SCATTERSPLITTER_H

#include "SimpSMTSolver.h"
#include "SplitData.h"
#include "SplitConfig.h"

class ScatterSplitter : public SimpSMTSolver {
public:
    std::vector<SplitData> splits;
    ScatterSplitter(SMTConfig & c, THandler & t);
private:
    std::vector<vec<Lit>> split_assumptions;
    SplitConfig splitConfig;
    void     updateSplitState();                                                       // Update the state of the splitting machine.
    bool     scatterLevel();                                                           // Are we currently on a scatter level.
    bool     createSplit_scatter(bool last);                                           // Create a split formula and place it to the splits vector.
    bool     excludeAssumptions(vec<Lit>& neg_constrs);                                // Add a clause to the database and propagate
    std::vector<Clause> toPublish_LearntClauses;
//    int      n_PublishedLearntClauses;
protected:
    virtual lbool solve_() override;
    virtual inline void clausesPublish() {
//        std::vector<Var> enabled_assumptions;
//
//        for (int i = 0; i < assumptions.size(); i++) {
//            if (sign(assumptions[i]))
//                enabled_assumptions.push_back(var(assumptions[i]));
//        }
//        int n_NotPublishedLearntClauses = learnts.size() - n_PublishedLearntClauses + n_reducedLearntClauses;
//        for (int i = learnts.size()-1 , j=0; j < n_NotPublishedLearntClauses ; i--,j++) {
//            CRef cr = learnts[i];
//            Clause &c = ca[cr];
//
//            bool intersected= false;
//            for (int j = 0; j < c.size(); j++) {
//                Lit &l = c[j];
//                uint8_t k;
//                for (k = 0; k < enabled_assumptions.size(); k++) {
//                    if (var(l) == enabled_assumptions[k]) {
//                        intersected= true;
//                        break;
//                    }
//                }
//                if (intersected)
//                    break;
//            }
//            if(!intersected) {
//                toPublish_LearntClauses.push_back(c);
//            }
//            n_PublishedLearntClauses++;
//        }

    };
protected:
    virtual inline void clausesUpdate() {};
    bool branchLitRandom() override;
    Var doActivityDecision() override;
    bool okContinue() const override;
    void runPeriodics();                // Update clauses
    lbool search(int nof_conflicts, int nof_learnts) override;                  // Search for a given number of conflicts.
    lbool zeroLevelConflictHandler() override;                                  // Common handling of zero-level conflict as it can happen at multiple places
};


#endif //OPENSMT_SCATTERSPLITTER_H
