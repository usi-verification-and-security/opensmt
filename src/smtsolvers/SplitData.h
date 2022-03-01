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
class SplitData
{
    bool                   no_instance;    // Does SplitData store the instance?

    std::vector<vec<Lit>>  constraints;    // The split constraints
    std::vector<vec<Lit>>  learnts;        // The learnt clauses

    static char* litToString(Lit);
    template<class C> char* clauseToString(const C&);
    char* clauseToString(const vec<Lit>&);
    static int getLitSize(Lit l);
    static std::vector<vec<PtAsgn>> toPTRefs(std::vector<vec<Lit>> const & in, const THandler &thandler);

public:
    SplitData(bool no_instance = true)
            : no_instance(no_instance)
    { assert(no_instance); }

    template<class C> void addConstraint(const C& c)
    {
        constraints.emplace_back();
        vec<Lit>& cstr = constraints.back();
        for (int i = 0; i < c.size(); i++)
            cstr.push(c[i]);
    }
    void addLearnt(Clause& c)
    {
        learnts.emplace_back();
        vec<Lit>& learnt = learnts.back();
        for (unsigned i = 0; i < c.size(); i++)
            learnt.push(c[i]);
    }

    char* splitToString();
    std::vector<vec<PtAsgn>> constraintsToPTRefs(const THandler& thandler) const { return toPTRefs(constraints, thandler); }
    std::vector<vec<PtAsgn>> learntsToPTRefs(const THandler& thandler) const { return toPTRefs(learnts, thandler); }
};

#endif //OPENSMT_SPLITDATA_H
