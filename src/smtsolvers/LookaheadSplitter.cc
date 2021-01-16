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

    score->updateRound();
    vec<LASplitNode*> queue;
    LASplitNode *root = new LASplitNode();
    root->p  = root;
    queue.push(root);

    while (queue.size() != 0)
    {
        LASplitNode* n = queue.last();
        queue.pop();
#ifdef LADEBUG
        printf("main loop: dl %d -> %d\n", decisionLevel(), 0);
#endif

        if (n->v == l_False) {
            deallocTree(n);
            continue;
        }

        switch (setSolverToNode(n)) {
            case PathBuildResult::pathbuild_tlunsat:
                deallocTree(n);
                return LALoopRes::unsat;
            case PathBuildResult::pathbuild_restart:
                deallocTree(n);
                return LALoopRes::restart;
            case PathBuildResult::pathbuild_unsat: {
                deallocTree(n);
                return LALoopRes::restart;
            }
            case PathBuildResult::pathbuild_success:
                ;
        }

        if (n->d == maxDepth)
        {
#ifdef LADEBUG
            printf("Producing a split:\n");;
            printTrace();
#endif
            createSplitLookahead(n);
            if (config.sat_split_test_cube_and_conquer())
                return LALoopRes::unsat; // The cube-and-conquer experiment
            else
                continue;
        }

        auto *c1 = new LASplitNode();
        auto *c2 = new LASplitNode();
        switch (expandTree(n, c1, c2)) {
            case laresult::la_tl_unsat:
                return LALoopRes::unsat;
            case laresult::la_restart:
                return LALoopRes::restart;
            case laresult::la_unsat:
                return LALoopRes::restart; // We restart for correctness (complicated?)
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
    copySplits(root);
    assert(static_cast<int>(splits.size()) == config.sat_split_num());
    return LALoopRes::unknown_final;
}

bool LookaheadSplitter::createSplitLookahead(LASplitNode *n)
{
    // Create a split instance and add it to node n.
    assert(n->sd == NULL);
    n->sd = new SplitData(config.smt_split_format_length() == spformat_brief);
    SplitData& sd = *n->sd;
    printf("; Outputing an instance:\n; ");
    Lit p = lit_Undef;
    for (int i = 0; i < decisionLevel(); i++)
    {
        vec<Lit> tmp;
        Lit l = trail[trail_lim[i]];
        if (p != l) {
            // In cases where the LA solver couldn't propagate due to
            // literal being already assigned, the literal may be
            // duplicated.  Do not report duplicates.
            tmp.push(l);
            printf("%s%d ", sign(l) ? "-" : "", var(l));
            sd.addConstraint(tmp);
        }
        p = l;
    }
    printf("\n");

    assert(ok);
    return true;
}

void LookaheadSplitter::copySplits(LASplitNode *root)
{
    if (root == nullptr)
        return;

    vec<LASplitNode*> queue;
    queue.push(root);

    Map <LASplitNode*,bool,LASplitNode::Hash> seen;

    // This is buggy: We need to pop the instances once all their children have been processed.
    while (queue.size() != 0) {
        LASplitNode* n = queue.last();
        if (!seen.has(n)) {
            seen.insert(n, true);
            if (n->c1 != nullptr) {
                assert(n->c2 != nullptr);
                queue.push(n->getC1());
                queue.push(n->getC2());
            }
            continue;
        }
        queue.pop();
        if (n->sd != nullptr) {
            splits.emplace_back(std::move(*n->sd));
            n->sd = nullptr;
        }
    }
}

