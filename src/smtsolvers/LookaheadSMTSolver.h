//
// Created by prova on 07.02.19.
//

#ifndef OPENSMT_LOOKAHEADSMTSOLVER_H
#define OPENSMT_LOOKAHEADSMTSOLVER_H

#include "SimpSMTSolver.h"
#include "LAScore.h"


class LookaheadSMTSolver : public SimpSMTSolver {
protected:
    ConflQuota confl_quota;
    int idx;

    // -----------------------------------------------------------------------------------------
    // Data type for exact value array
    static inline int min(int i, int j) { return i < j ? i : j; }
    static inline int max(int i, int j) { return i > j ? i : j; }
    class LANode
    {
    public:
        // c1 & c2 are for garbage collection
        LANode* c1;
        LANode* c2;
        const LANode* p;
        Lit l;
        lbool v;
        int d;
        LANode() : c1(nullptr), c2(nullptr), p(nullptr), l(lit_Undef), v(l_Undef), d(0) {}
        LANode(LANode&& o) : c1(o.c1), c2(o.c2), p(o.p), l(o.l), v(o.v), d(o.d) {}
        LANode& operator=(const LANode& o) { c1 = o.c1; c2 = o.c2; p = o.p; l = o.l; v = o.v; d = o.d; return *this; }
        LANode(const LANode* par, Lit li, lbool va, int dl) :
            c1(nullptr), c2(nullptr), p(par), l(li), v(va), d(dl) {}

        virtual void print_local() {
            for (int i = 0; i < d; i++)
                dprintf(STDERR_FILENO, " ");
            dprintf(STDERR_FILENO, "%s%d [%s, %d]", sign(l) ? "-" : "", var(l), v == l_False ? "unsat" : "open", d);

            if (c1 != nullptr)
            {
                dprintf(STDERR_FILENO, " c1");
            }
            if (c2 != nullptr)
            {
                dprintf(STDERR_FILENO, " c2");
            }
            dprintf(STDERR_FILENO, "\n");
        }

        void print()
        {
            print_local();

            if (c1 != nullptr)
                c1->print();
            if (c2 != nullptr)
                c2->print();
        }
        struct Hash {
            uint32_t operator ()(const LANode *p) const { return (uint32_t)(unsigned int long)p/sizeof(unsigned int long); }
        };
    };
    lbool    laPropagateWrapper();


protected:
    // The result from the lookahead loop
    enum class LALoopRes
    {
        sat,
        unsat,
        unknown,
        unknown_final,
        restart
    };

    enum class laresult
    {
        la_tl_unsat,
        la_sat,
        la_restart,
        la_unsat,
        la_ok
    };

    virtual LALoopRes solveLookahead();
    laresult lookaheadLoop   (Lit& best);
    lbool solve_() override;                                                            // Does not change the formula

    enum class PathBuildResult {
        pathbuild_success,
        pathbuild_tlunsat,
        pathbuild_unsat,
        pathbuild_restart
    };

    PathBuildResult setSolverToNode(LANode *n);                                         // Set solver dl stack according to the path from root to n
    laresult expandTree(LANode *n, LANode *c1, LANode *c2);                             // Do lookahead.  On success write the new children to c1 and c2
    void deallocTree(LANode *n);                                                        // Dealloc the tree rooted at n
    LookaheadScoreClassic score;
public:
    LookaheadSMTSolver(SMTConfig&, THandler&);
    Var newVar(bool sign, bool dvar) override;
};


#endif //OPENSMT_LOOKAHEADSMTSOLVER_H
