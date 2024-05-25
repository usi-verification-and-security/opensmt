/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_SPLITDATA_H
#define PARALLEL_SPLITDATA_H

#include "THandler.h"
#include <minisat/core/SolverTypes.h>

// -----------------------------------------------------------------------------------------
// The splits
//

class SplitData {
    std::vector<vec<Lit>>  constraints;    // The constraints are the assumptions from previous splits
    std::vector<vec<Lit>>  split_assumptions; // The assumptions in this split

    static void addClausesToPtAsgns(std::vector<vec<PtAsgn>> & out, std::vector<vec<Lit>> const & in, THandler const & thandler) {
        for (vec<Lit> const & c : in) {
            vec<PtAsgn> outClause;
            outClause.capacity(c.size());
            for (Lit l : c) {
                PTRef tr = thandler.varToTerm(var(l));
                PtAsgn pta(tr, sign(l) ? l_False : l_True);
                outClause.push(pta);
            }
            out.push_back(std::move(outClause));
        }
    }

public:
    void addConstraint(vec<Lit> && c) {
        constraints.emplace_back(std::move(c));
    }

    void addSplitAssumptions(vec<Lit> && sa) {
        split_assumptions.emplace_back(std::move(sa));
    }

    [[nodiscard]] std::vector<vec<PtAsgn>> splitToPtAsgns(THandler const & thandler) const {
        std::vector<vec<PtAsgn>> out;
        addClausesToPtAsgns(out, constraints, thandler);
        addClausesToPtAsgns(out, split_assumptions, thandler);
        return out;
    }

    std::vector<vec<Lit>> & getSplitAssumptions()               { return split_assumptions; }
    [[nodiscard]] std::vector<vec<Lit>> const & peekSplitAssumptions() const  { return split_assumptions; }
};

#endif //PARALLEL_SPLITDATA_H
