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

    std::vector<vec<PtAsgn>> splitToPtAsgns(const THandler& thandler) const {
        std::vector<vec<PtAsgn>> out;
        addClausesToPtAsgns(out, constraints, thandler);
        addClausesToPtAsgns(out, split_assumptions, thandler);
        return out;
    }

    std::vector<vec<Lit>> & getSplitAssumptions()               { return split_assumptions; }
    std::vector<vec<Lit>> const & peekSplitAssumptions() const  { return split_assumptions; }

    vec<Lit> &              getSplitAssumption(std::size_t i)   { return split_assumptions[i]; }
};

#endif //PARALLEL_SPLITDATA_H
