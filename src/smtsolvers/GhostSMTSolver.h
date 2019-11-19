//
// Created by prova on 14.11.19.
//

#ifndef OPENSMT_GHOSTSMTSOLVER_H
#define OPENSMT_GHOSTSMTSOLVER_H
#include "SimpSMTSolver.h"

class GhostSMTSolver : public SimpSMTSolver
{
private:
    vec<vec<CRef>> thLitToClauses;
    vec<Var> ghostTrail;
    vec<int> ghostTrailLim;
    Var pickBranchVar();
    Var pickRandomBranchVar();
    Lit pickBranchPolarity(Var v);
    bool isGhost(Lit l);
protected:
    void attachClause      (CRef)      override;
    void detachClause      (CRef, bool strict) override;
    Lit  pickBranchLit     ()          override;
    void newDecisionLevel  ()          override;
    void cancelUntil       (int level) override;
    Var  newVar            (bool polarity, bool dvar) override;
    void verifyModel       () override;
public:
    GhostSMTSolver(SMTConfig& c, THandler& h) : SimpSMTSolver(c, h) {}
    void garbageCollect() override;
    void relocAll();
};

#endif //OPENSMT_GHOSTSMTSOLVER_H
