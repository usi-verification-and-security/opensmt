//
// Created by prova on 08.03.22.
//

#ifndef OPENSMT_SMTSOLVER_H
#define OPENSMT_SMTSOLVER_H

#include "SolverTypes.h"
#include "THandler.h"
#include "Proof.h"

class SMTSolver {
protected:
    THandler & theory_handler;

public:
    SMTSolver(THandler & tHandler) : theory_handler(tHandler) {}
    virtual ~SMTSolver() {};
    virtual int nVars() const = 0;
    virtual int nClauses() const = 0;
    bool stop = false;
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
};


#endif //OPENSMT_SMTSOLVER_H
