//
// Created by prova on 08.02.19.
//

#include "LookaheadSplitter.h"
// The new try for the lookahead with backjumping:
// Do not write this as a recursive function but instead maintain the
// tree explicitly.  Each internal node should have the info whether its
// both children have been constructed and whether any of its two
// children has been shown unsatisfiable either directly or with a
// backjump.
//
// The parameter d is the maximum depth of a path, used for splitting.
// If d < 0, there is no maximum depth and the search continues on a
// branch until it is shown unsatisfiable.
//
LookaheadSMTSolver::LALoopRes LookaheadSplitter::solveLookahead()
{

    int maxDepth = getLog2Ceil(config.sat_split_num());

    updateRound();
    vec<LANode*> queue;
    LANode *root = new LANode();
    root->p  = root;
    queue.push(root);

    while (queue.size() != 0)
    {
        LANode* n = queue.last();
        queue.pop();
#ifdef LADEBUG
        printf("main loop: dl %d -> %d\n", decisionLevel(), 0);
#endif

        if (n->v == l_False)
            continue;

        switch (setSolverToNode(n)) {
            case PathBuildResult::pathbuild_tlunsat:
                return LALoopRes::unsat;
            case PathBuildResult::pathbuild_restart:
                return LALoopRes::restart;
            case PathBuildResult::pathbuild_unsat:
                continue;
            case PathBuildResult::pathbuild_success:
                ;
        }

        if (n->d == maxDepth)
        {
#ifdef LADEBUG
            printf("Producing a split:\n");;
            printTrace();
#endif
            createSplitLookahead();
            if (config.sat_split_test_cube_and_conquer())
                return LALoopRes::unsat; // The cube-and-conquer experiment
            else
                continue;
        }

        LANode *c1 = new LANode();
        LANode *c2 = new LANode();
        switch (expandTree(n, *c1, *c2)) {
            case laresult::la_tl_unsat:
                return LALoopRes::unsat;
            case laresult::la_restart:
                return LALoopRes::restart;
            case laresult::la_unsat:
                queue.push(n);
                continue;
            case laresult::la_sat:
                return LALoopRes::sat;
            case laresult::la_ok:
                ;
        }

        queue.push(c1);
        queue.push(c2);
    }
#ifdef LADEBUG
    root->print();
#endif
    return LALoopRes::unknown;
}

