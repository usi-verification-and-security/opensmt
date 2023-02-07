//
// Created by prova on 07.02.19.
//

#ifndef OPENSMT_PICKYSMTSOLVER_H
#define OPENSMT_PICKYSMTSOLVER_H

#include "LookaheadSMTSolver.h"
#include "LAScore.h"

#include <memory>
#include <unistd.h>

class PickySMTSolver : public LookaheadSMTSolver {
protected:
    int idx;
    int crossed_assumptions;

protected:
    // The result from the lookahead loop

    template<typename Node, typename BuildConfig>
    std::pair<LALoopRes, std::unique_ptr<Node>> buildAndTraverse(BuildConfig &&);

    virtual LALoopRes solvePicky();
    std::pair<laresult,Lit> lookaheadLoop();
    virtual void cancelUntil(int level) override; // Backtrack until a certain level.
    lbool solve_() override; // Does not change the formula

    PathBuildResult setSolverToNode(LANode const &);                                         // Set solver dl stack according to the path from root to n
    laresult expandTree(LANode & n, std::unique_ptr<LANode> c1, std::unique_ptr<LANode> c2); // Do lookahead.  On success write the new children to c1 and c2
    void rebuildOrderHeap();
    std::unique_ptr<LookaheadScore> score;
public:
    PickySMTSolver(SMTConfig&, THandler&);
    Var newVar(bool dvar) override;
};

// Maintain the tree explicitly.  Each internal node should have the info whether its
// both children have been constructed and whether any of its two
// children has been shown unsatisfiable either directly or with a
// backjump.
template<typename Node, typename BuildConfig>
std::pair<PickySMTSolver::LALoopRes, std::unique_ptr<Node>>
PickySMTSolver::buildAndTraverse(BuildConfig && buildConfig) {
    score->updateRound();
    vec<Node *> queue;
    auto * root_raw = new Node();
    auto root = std::unique_ptr<Node>(root_raw);
    root->p = root_raw;
    queue.push(root_raw);

    while (queue.size() != 0) {
        Node * n = queue.last();
        queue.pop();
        assert(n);

        switch (setSolverToNode(*n)) {
            case PathBuildResult::pathbuild_tlunsat:
                return { LALoopRes::unsat, nullptr };
            case PathBuildResult::pathbuild_restart:
                return { LALoopRes::restart, nullptr };
            case PathBuildResult::pathbuild_unsat: {
                // Reinsert the parent to the queue
                assert(n != root_raw); // Unsatisfiability in root should be tlunsat
                Node * parent = n->getParent();
                if (queue.size() > 0 and queue.last()->p == parent) {
                    // This is the second child (searched first).  Pop the other child as well
                    queue.pop();
                    // Now queue does not have children of the parent
                    assert( std::all_of(queue.begin(), queue.end(), [parent] (Node const * qel) { return qel->p != parent; }) );
                }
                queue.push(parent);
                parent->c1.reset(nullptr);
                parent->c2.reset(nullptr);
                continue;
            }
            case PathBuildResult::pathbuild_success:
                ;
        }

        assert(n);

        if (buildConfig.stopCondition(*n, config.sat_split_num())) {
            continue;
        }

        auto c1_raw = new Node();
        auto c2_raw = new Node();
        auto c1 = std::unique_ptr<Node>(c1_raw);
        auto c2 = std::unique_ptr<Node>(c2_raw);
        bool checked = false;

        if(crossed_assumptions < assumptions.size()){
            while (crossed_assumptions < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[crossed_assumptions];
                if (value(p) == l_True) {
                    // Dummy decision level:
                    crossed_assumptions++;
                } else if (value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    int max = 0;
                    for (Lit q : conflict) {
                        if (!sign(q)) {
                            max = assumptions_order[var(q)] > max ? assumptions_order[var(q)] : max;
                        }
                    }
                    conflict_frame = max+1;
                    ok = false;
                    return { LALoopRes::unsat, nullptr };
                } else {
                    c1_raw->p = n;
                    c1_raw->d = (*n).d + 1;
                    c1_raw->l = p;
                    n->c1 = std::move(c1);
                    crossed_assumptions++;
                    checked = true;
                    queue.push(c1_raw);
                    break;
                }
            }
        }

        if(!checked) {
            switch (expandTree(*n, std::move(c1), std::move(c2))) {
            case laresult::la_tl_unsat:
                return {LALoopRes::unsat, nullptr};
            case laresult::la_restart:
                return {LALoopRes::restart, nullptr};
            case laresult::la_unsat:
                queue.push(n);
                continue;
            case laresult::la_sat:
                return {LALoopRes::sat, nullptr};
            case laresult::la_ok:;
            }

            queue.push(c1_raw);
            queue.push(c2_raw);
        }
    }
#ifdef PDEBUG
    root->print();
#endif
    return { buildConfig.exitState(), std::move(root) };
}


#endif //OPENSMT_PICKYSMTSOLVER_H
