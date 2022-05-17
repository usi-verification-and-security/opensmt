/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_SPLITDATA_H
#define PARALLEL_SPLITDATA_H

#include "SolverTypes.h"
#include "THandler.h"

// -----------------------------------------------------------------------------------------
// The splits
//

class SplitData {
    std::vector<vec<Lit>>  constraints;    // The split constraints
    std::vector<vec<Lit>>  learnts;        // The learnt clauses
    std::vector<vec<Lit>>  split_assumptions;

    static char* litToString(Lit);
    template<class C> char* clauseToString(C const &);
    char* clauseToString(const vec<Lit>&);
    static int getLitSize(Lit l);
    static std::vector<vec<PtAsgn>> toPTRefs(std::vector<vec<Lit>> const & in, THandler const & thandler);

public:
    template<class C> void addConstraint(const C& c) {
        vec<Lit> cstr;
        for (Lit l : c) {
            cstr.push(l);
        }
        constraints.emplace_back(std::move(cstr));
    }

    template<class C> void addSplitAssumptions(const C& sa) {
        vec<Lit> vl;
        for (Lit l : sa) {
            vl.push(l);
        }
        split_assumptions.emplace_back(std::move(vl));
    }

    char* splitToString();
    std::vector<vec<PtAsgn>> constraintsToPTRefs(const THandler& thandler) const { return toPTRefs(constraints, thandler); }

    std::vector<vec<Lit>> & getSplitAssumptions()               { return split_assumptions; }

    vec<Lit> &              getSplitAssumption(std::size_t i)   { return split_assumptions[i]; }
};

#endif //PARALLEL_SPLITDATA_H
