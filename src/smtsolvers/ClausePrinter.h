//
// Created by prova on 08.03.22.
//

#ifndef OPENSMT_CLAUSEPRINTER_H
#define OPENSMT_CLAUSEPRINTER_H

#include "SMTSolver.h"

class ClausePrinter : public SMTSolver {
    std::vector<vec<Lit>> clauses;
    void addVar(Var v) override;
    Map<Var, bool, VarHash> vars;
    int numberOfVars;
public:
    ClausePrinter(SMTConfig &, THandler & tHandler) : SMTSolver(tHandler) {}
    ~ClausePrinter() = default;
    int nVars() const override { return numberOfVars; }
    int nClauses() const override { return clauses.size(); }
    bool isOK() const override { return true; }
    void restoreOK() override { }
    lbool solve(vec<Lit> const & assumps) override;
    bool addOriginalSMTClause(vec<Lit> const & smtClause, opensmt::pair<CRef, CRef> & inOutCRefs) override;
    lbool modelValue(Lit) const override { return l_Undef; }
    void fillBooleanVars(ModelBuilder &) override { throw OsmtApiException("ClausePrinter does not support model building"); }
    void initialize() override {}
    void clearSearch() override {}
    Proof const & getProof() const override { throw OsmtApiException("ClausePrinter does not support proof production"); }
    int getConflictFrame() const override { throw OsmtApiException("ClausePrinter does not support satisfiability checking"); }
};

#endif //OPENSMT_CLAUSEPRINTER_H
