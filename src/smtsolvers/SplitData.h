//
// Created by prova on 31.03.21.
//

#ifndef OPENSMT_SPLITDATA_H
#define OPENSMT_SPLITDATA_H

#include "SolverTypes.h"
#include "THandler.h"

// -----------------------------------------------------------------------------------------
// The splits
//

class SplitData {
    std::vector<vec<Lit>>  constraints;    // The split constraints
    std::vector<vec<Lit>>  learnts;        // The learnt clauses

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

    char* splitToString();
    std::vector<vec<PtAsgn>> constraintsToPTRefs(const THandler& thandler) const { return toPTRefs(constraints, thandler); }
};

#endif //OPENSMT_SPLITDATA_H
