//
// Created by prova on 07.02.19.
//

#ifndef OPENSMT_LOOKAHEADSMTSOLVER_H
#define OPENSMT_LOOKAHEADSMTSOLVER_H

#include "LAScore.h"
#include "SimpSMTSolver.h"

#include <memory>
#include <unistd.h>

namespace opensmt {
class LookaheadSMTSolver : public SimpSMTSolver {
protected:
    ConflQuota confl_quota;
    int idx;
    int crossed_assumptions;

    // -----------------------------------------------------------------------------------------
    // Data type for exact value array
    static inline int min(int i, int j) { return i < j ? i : j; }
    static inline int max(int i, int j) { return i > j ? i : j; }
    class LANode {
    public:
        // The children
        std::unique_ptr<LANode> c1;
        std::unique_ptr<LANode> c2;
        LANode * p;
        virtual LANode * getParent() { return p; }
        Lit l;
        int d;
        LANode() : l(lit_Undef), d(0) {}
        virtual ~LANode() = default;
        virtual void print_local() const {
            for (int i = 0; i < d; i++)
                dprintf(STDERR_FILENO, " ");
            dprintf(STDERR_FILENO, "%s%d [%d]", sign(l) ? "-" : "", var(l), d);

            if (c1 != nullptr) { dprintf(STDERR_FILENO, " c1"); }
            if (c2 != nullptr) { dprintf(STDERR_FILENO, " c2"); }
            dprintf(STDERR_FILENO, "\n");
        }

        void print() const {
            print_local();
            if (c1 != nullptr) c1->print();
            if (c2 != nullptr) c2->print();
        }
    };

    lbool laPropagateWrapper();

protected:
    // The result from the lookahead loop
    enum class LALoopRes { sat, unsat, unknown, unknown_final, restart };

    enum class laresult { la_tl_unsat, la_sat, la_restart, la_unsat, la_ok };

    template<typename Node, typename BuildConfig>

    std::pair<LALoopRes, std::unique_ptr<Node>> buildAndTraverse(BuildConfig &&);

    virtual LALoopRes solveLookahead();
    std::pair<laresult, Lit> lookaheadLoop();
    virtual void cancelUntil(int level) override; // Backtrack until a certain level.
    lbool solve_() override;                      // Does not change the formula

    enum class PathBuildResult { pathbuild_success, pathbuild_tlunsat, pathbuild_unsat, pathbuild_restart };

    PathBuildResult setSolverToNode(LANode const &); // Set solver dl stack according to the path from root to n
    laresult expandTree(LANode & n, std::unique_ptr<LANode> c1,
                        std::unique_ptr<LANode> c2); // Do lookahead.  On success write the new children to c1 and c2
    std::unique_ptr<LookaheadScore> score;
    bool okToPartition(Var) const { return true; }

public:
    LookaheadSMTSolver(SMTConfig &, THandler &);
    Var newVar(bool dvar) override;
};

// Maintain the tree explicitly.  Each internal node should have the info whether its
// both children have been constructed and whether any of its two
// children has been shown unsatisfiable either directly or with a
// backjump.
template<typename Node, typename BuildConfig>
std::pair<LookaheadSMTSolver::LALoopRes, std::unique_ptr<Node>>
LookaheadSMTSolver::buildAndTraverse(BuildConfig && buildConfig) {
    score->updateRound();
    vec<Node *> queue;
    auto * root_raw = new Node();
    auto root = std::unique_ptr<Node>(root_raw);
    root->p = root_raw;
    queue.push(root_raw);
    TPropRes res = checkTheory(true);
    if (res == TPropRes::Unsat) {
        return {LALoopRes::unsat, nullptr}; // unsat
    }

    while (queue.size() != 0) {
        Node * n = queue.last();
        queue.pop();
        assert(n);

        switch (setSolverToNode(*n)) {
            case PathBuildResult::pathbuild_tlunsat:
                return {LALoopRes::unsat, nullptr};
            case PathBuildResult::pathbuild_restart:
                return {LALoopRes::restart, nullptr};
            case PathBuildResult::pathbuild_unsat: {
                // Reinsert the parent to the queue
                assert(n != root_raw); // Unsatisfiability in root should be tlunsat
                Node * parent = n->getParent();
                if (queue.size() > 0 and queue.last()->p == parent) {
                    // This is the second child (searched first).  Pop the other child as well
                    queue.pop();
                    // Now queue does not have children of the parent
                    assert(std::all_of(queue.begin(), queue.end(),
                                       [parent](Node const * qel) { return qel->p != parent; }));
                }
                queue.push(parent);
                parent->c1.reset(nullptr);
                parent->c2.reset(nullptr);
                continue;
            }
            case PathBuildResult::pathbuild_success:;
        }

        assert(n);

        if (buildConfig.stopCondition(*n, config.sat_split_num())) { continue; }

        auto c1_raw = new Node();
        auto c2_raw = new Node();
        auto c1 = std::unique_ptr<Node>(c1_raw);
        auto c2 = std::unique_ptr<Node>(c2_raw);
        bool checked = false;

        if (crossed_assumptions < assumptions.size()) {
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
                        if (!sign(q)) { max = assumptions_order[var(q)] > max ? assumptions_order[var(q)] : max; }
                    }
                    conflict_frame = max + 1;
                    ok = false;
                    return {LALoopRes::unsat, nullptr};
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

        if (!checked) {
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
    return {buildConfig.exitState(), std::move(root)};
}
} // namespace opensmt

#endif // OPENSMT_LOOKAHEADSMTSOLVER_H
