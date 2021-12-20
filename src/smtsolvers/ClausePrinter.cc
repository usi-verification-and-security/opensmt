/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ClausePrinter.h"
#include "Proof.h"

lbool ClausePrinter::solve(vec<Lit> const &) {
    // print all clauses
    std::cout << "p cnf " + std::to_string(nVars()) + " " + std::to_string(nClauses()) << std::endl;
    for (vec<Lit> const & smtClause : clauses) {
        for (Lit l: smtClause) {
            Var v = var(l);
            std::cout << (sign(l) ? -(v + 1) : (v + 1)) << " ";
        }
        std::cout << "0" << std::endl;
    }
    return l_Undef;
}

void ClausePrinter::addVar(Var v) {
    if (not vars.has(v)) {
        vars.insert(v, true);
        ++ numberOfVars;
    }
}

bool ClausePrinter::addOriginalSMTClause(vec<Lit> const & smtClause, opensmt::pair<CRef, CRef> &) {
    // Add a clause
    for (Lit l : smtClause) {
        Var v = var(l);
        if (not vars.has(v)) {
            vars.insert(v, true);
            numberOfVars++;
        }
    }
    vec<Lit> outClause;
    smtClause.copyTo(outClause);
    clauses.push_back(std::move(outClause));
    return true;
}
