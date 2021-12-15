//
// Created by prova on 08.03.22.
//

#ifndef OPENSMT_CLAUSEPRINTER_H
#define OPENSMT_CLAUSEPRINTER_H

#include "SMTSolver.h"

class ModelCounter : public SMTSolver {
    std::vector<vec<Lit>> clauses;
    void addVar(Var v) override;
    Map<Var, bool, VarHash> vars;
    int numberOfVarsSeen;
    std::unordered_map<PTRef, std::unordered_set<Var>, PTRefHash> bvTermToVars;
public:
    ModelCounter(SMTConfig &, THandler & tHandler) : SMTSolver(tHandler), numberOfVarsSeen(0) {}
    int nVars() const override { return numberOfVarsSeen; }
    int nClauses() const override { return clauses.size(); }
    bool isOK() const override { return true; }
    void restoreOK() override { }
    lbool solve(vec<Lit> const &) override { throw OsmtApiException("ModelCounter does not support satisfiability checking"); };
    bool addOriginalSMTClause(vec<Lit> const & smtClause, opensmt::pair<CRef, CRef> & inOutCRefs) override;
    lbool modelValue(Lit) const override { return l_Undef; }
    void fillBooleanVars(ModelBuilder &) override { throw OsmtApiException("ModelCounter does not support model building"); }
    void initialize() override {}
    void clearSearch() override {}
    Proof const & getProof() const override { throw OsmtApiException("ModelCounter does not support proof production"); }
    int getConflictFrame() const override { throw OsmtApiException("ModelCounter does not support satisfiability checking"); }
    void count(vec<PTRef> const & terms) const;
};

#endif //OPENSMT_CLAUSEPRINTER_H
