/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_SMTSOLVER_H
#define OPENSMT_SMTSOLVER_H

#include "SolverTypes.h"
#include "THandler.h"
#include "Proof.h"

class SMTSolver {
protected:
    THandler & theory_handler;
    bool stop = false;
public:
    SMTSolver(THandler & tHandler) : theory_handler(tHandler) {}
    virtual ~SMTSolver() {};
    virtual int nVars() const = 0;
    virtual int nClauses() const = 0;
    virtual bool isOK() const = 0;
    virtual void restoreOK() = 0;
    virtual lbool solve(vec<Lit> const & assumps) = 0;
    virtual void addVar(Var) = 0;
    virtual bool addOriginalSMTClause(vec<Lit> const & clause, opensmt::pair<CRef, CRef> & iorefs) = 0;
    virtual lbool modelValue(Lit l) const = 0;
    virtual void fillBooleanVars(ModelBuilder & modelBuilder) = 0;
    virtual void initialize() = 0;
    virtual void clearSearch() = 0;  // Backtrack SAT solver and theories to decision level 0
    virtual Proof const & getProof() const = 0;
    virtual int getConflictFrame() const = 0;
    void setStop() { stop = true; }
    virtual void mapEnabledFrameIdToVar(Var, uint32_t, uint32_t &)  { return; }
    virtual void addAssumptionVar(Var)                              { return; }
};


#endif //OPENSMT_SMTSOLVER_H
