//
// Created by prova on 07.02.19.
//
#include <chrono>
#include "LookaheadSMTSolver.h"
#include "Proof.h"

LookaheadSMTSolver::LookaheadSMTSolver(SMTConfig & c, THandler & thandler)
    : SimpSMTSolver(c, thandler), idx(0),
      score(c.lookahead_score_deep() ? (LookaheadScore *)(new LookaheadScoreDeep(assigns, c))
                                     : (LookaheadScore *)(new LookaheadScoreClassic(assigns, c))) {}

Var LookaheadSMTSolver::newVar(bool dvar) {
    Var v = SimpSMTSolver::newVar(dvar);
    score->newVar();
    return v;
}

lbool LookaheadSMTSolver::solve_() {
    for (Lit l : this->assumptions) {
        this->addVar_(var(l));
    }

    declareVarsToTheories();

    double nof_conflicts = restart_first;
    crossed_assumptions = 0;
    LALoopRes res = LALoopRes::unknown;

    model.clear();
    conflict.clear();

    while (res == LALoopRes::unknown || res == LALoopRes::restart) {
        res = solveLookahead();

        nof_conflicts = restartNextLimit(nof_conflicts);
    }

    if (res == LALoopRes::sat) {
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) {
            model[i] = value(i);
        }
    } else {
        assert(not okContinue() || res == LALoopRes::unsat || this->stop);
    }
    switch (res) {
        case LALoopRes::unknown_final:
            return l_Undef;
        case LALoopRes::sat:
            return l_True;
        case LALoopRes::unsat: {
            ok = false;
            return l_False;
        }
        default:
            assert(false);
            return l_Undef;
    }
}

//
// Function for making a propagation.
// max_confl is a bound on the number of conflicts the wrapper is allowed to do
// Returns l_Undef if the bound on conflicts is reached.
// Returns l_False if the there was a conflict.
// Returns l_True if there was no conflict.
//
// Backtracks the solver to the correct decision level and continues until no
// new conflicts or propagations are available in theory or in unit propagation
//

lbool LookaheadSMTSolver::laPropagateWrapper() {
    CRef cr;
    bool diff;
    do {
        diff = false;
        while ((cr = propagate()) != CRef_Undef) {
            if (decisionLevel() == 0) return l_False; // Unsat
            --confl_quota;
            // Received a conflict and decisionLevel > 0
            if (confl_quota <= 0) return l_Undef;

            vec<Lit> out_learnt;
            int out_btlevel;
            analyze(cr, out_learnt, out_btlevel);
            // Backtracking back to the second best decision level in the clause
            cancelUntil(out_btlevel);
            assert(value(out_learnt[0]) == l_Undef);
            if (out_learnt.size() == 1) {
                CRef unitClause = ca.alloc(vec<Lit>{out_learnt[0]});
                if (logsProofForInterpolation()) { proof->endChain(unitClause); }
                uncheckedEnqueue(out_learnt[0], unitClause);
            } else {
                CRef crd = ca.alloc(out_learnt, {true, computeGlue(out_learnt)});
                if (logsProofForInterpolation()) { proof->endChain(crd); }
                learnts.push(crd);
                attachClause(crd);
                uncheckedEnqueue(out_learnt[0], crd);
            }
            diff = true;
        }
        if (!diff) {
            TPropRes res = checkTheory(true);
            if (res == TPropRes::Unsat) {
                return l_False; // Unsat
            } else if (res == TPropRes::Propagate) {
                diff = true;
                --confl_quota;
                if (confl_quota <= 0) return l_Undef;
            }
        }
    } while (diff);

    return l_True;
}

/**
 * Set solver decision stack according to the path from the root to @param n.
 * As a side-effect the solver is either
 * (i)  set to the path, or
 * (ii) a node in the path is marked closed, meaning that there are no solutions in extensions of the path.
 * In case (i) @return pathbuild_success
 * In case (ii), either @return pathbuild_tlunsat or @return pathbuild_unsat
 *
 */
LookaheadSMTSolver::PathBuildResult LookaheadSMTSolver::setSolverToNode(LANode const & n) {
    vec<Lit> path;
    LANode const * curr = &n;
    LANode const * parent = n.p;
    // Collect the truth assignment.
    while (parent != curr) {
        path.push(curr->l);
        curr = parent;
        parent = curr->p;
    }
    // setting solver to the correct dl
    int i = 0;
    if (path.size() <= decisionLevel()) {
        // Means we've encountered conflict and backtracked to another path in DPLL
        // New path is different from the old one only in the last element
        if (path.size() > 0) {
            cancelUntil(path.size() - 1);
        } else {
            cancelUntil(0);
        }
        crossed_assumptions = std::min(path.size(), assumptions.size());
    } else {
        // Means no conflict was encountered and basic path hasn't changed
        // we need only propagate i new literals
        i = (path.size() - decisionLevel()) - 1;
    }
    if (path.size() > 0) {
        for (; i >= 0; i--) {
            newDecisionLevel();
            if (value(path[i]) == l_Undef) {
                // propagating path[i]
                int curr_dl = decisionLevel();
                uncheckedEnqueue(path[i]);
                lbool res = laPropagateWrapper();
                // Here it is possible that the solver is on level 0 and in an inconsistent state.  How can I check
                // this?
                if (res == l_False) {
                    return PathBuildResult::pathbuild_tlunsat; // Indicate unsatisfiability
                } else if (res == l_Undef) {
                    cancelUntil(0);
                    return PathBuildResult::pathbuild_restart; // Do a restart
                }
                if (curr_dl != decisionLevel()) { return PathBuildResult::pathbuild_unsat; }
            } else {
                // literal to propagate was already assigned
                if (value(path[i]) == l_False) {
                    return PathBuildResult::pathbuild_unsat;
                } else {
                    assert(value(path[i]) == l_True);
                }
            }
        }
        if (config.sat_picky()) { rebuildOrderHeap(); }
    }
    return PathBuildResult::pathbuild_success;
}

LookaheadSMTSolver::laresult LookaheadSMTSolver::expandTree(LANode & n, std::unique_ptr<LANode> c1,
                                                            std::unique_ptr<LANode> c2) {
    assert(c1);
    assert(c2);
    // Do the lookahead
    assert(decisionLevel() == n.d);
    auto [res, best] = lookaheadLoop();
    while (best == lit_Undef && res == laresult::la_ok) {
        std::tie(res, best) = lookaheadLoop();
    };
    assert(best != lit_Undef || res != laresult::la_ok);
    assert(decisionLevel() <= n.d);
    if (res != laresult::la_ok) return res;

    assert(best != lit_Undef);

    c1->p = &n;
    c1->d = n.d + 1;
    c1->l = best;
    c2->p = &n;
    c2->d = n.d + 1;
    c2->l = ~best;
    n.c1 = std::move(c1);
    n.c2 = std::move(c2);

    return laresult::la_ok;
}

LookaheadSMTSolver::LALoopRes LookaheadSMTSolver::solveLookahead() {
    struct PlainBuildConfig {
        bool stopCondition(LANode &, int) { return false; }
        LALoopRes exitState() const { return LALoopRes::unknown; }
    };
    return buildAndTraverse<LANode, PlainBuildConfig>(PlainBuildConfig()).first;
};

std::pair<LookaheadSMTSolver::laresult, Lit> LookaheadSMTSolver::lookaheadLoop() {
//    if(clauses_num*2 <= clauses.size()) {
//        clauses_num = clauses.size();
//        auto start = std::chrono::steady_clock::now();
//        int pickyWidth = std::min(nVars(), config.sat_picky_w());
//        ConflQuota prev = confl_quota;
//        confl_quota = ConflQuota(); // Unlimited;
//        if (laPropagateWrapper() == l_False) {
//            // already unsat at the point of entering loop
//            return {laresult::la_tl_unsat, lit_Undef};
//        }
//        confl_quota = prev;
//
//        score->updateRound();
//        int i = 0;
//        int d = decisionLevel();
//
//        bool respect_logic_partitioning_hints = config.respect_logic_partitioning_hints();
//        int skipped_vars_due_to_logic = 0;
//
//        if (config.sat_picky()) {
//            int k = 0, j = 0;
//            while (k < order_heap.size() && j < pickyWidth) {
//                if (value(order_heap[k]) == l_Undef) {
//                    j++;
//                    k++;
//                } else {
//                    order_heap.remove(order_heap[k]);
//                }
//            }
//            if (order_heap.size() == 0) { return {laresult::la_sat, lit_Undef}; }
//            pickyWidth = std::min(order_heap.size(), pickyWidth);
//        }
//        for (Var v(idx % nVars()); !score->isAlreadyChecked(v);
//             v = config.sat_picky() ? order_heap[(idx + (++i)) % pickyWidth] : Var((idx + (++i)) % nVars())) {
//            if (!decision[v]) {
//                score->setChecked(v);
//                // not a decision var
//                continue;
//            }
//            if (v == (idx * nVars()) && skipped_vars_due_to_logic > 0)
//                respect_logic_partitioning_hints = false; // Allow branching on these since we looped back.
//            if (respect_logic_partitioning_hints && !okToPartition(v)) {
//                skipped_vars_due_to_logic++;
//                std::cout << "Skipping " << v << " since logic says it's not good\n";
//                continue; // Skip the vars that the logic considers bad to split on
//            }
//            // checking the variable score
//            Lit best = score->getBest();
//            if (value(v) != l_Undef || (best != lit_Undef && score->safeToSkip(v, best))) {
//                score->setChecked(v);
//                // It is possible that all variables are assigned here.
//                // In this case it seems that we have a satisfying assignment.
//                // This is in fact a debug check
//                if (static_cast<unsigned int>(trail.size()) == dec_vars) {
//                    // checking if all vars are set
//                    if (checkTheory(true) != TPropRes::Decide)
//                        return {laresult::la_tl_unsat, lit_Undef}; // Problem is trivially unsat
//                    assert(checkTheory(true) == TPropRes::Decide);
//    #ifndef NDEBUG
//                    for (CRef cr : clauses) {
//                        Clause & c = ca[cr];
//                        unsigned k;
//                        for (k = 0; k < c.size(); k++) {
//                            if (value(c[k]) == l_True) { break; }
//                        }
//                        assert(k < c.size());
//                    }
//    #endif
//                    return {laresult::la_sat, lit_Undef}; // Stands for SAT
//                }
//                continue;
//            }
//            if (trail.size() == nVars() + skipped_vars_due_to_logic) {
//                std::cout << "; " << skipped_vars_due_to_logic << " vars were skipped\n";
//                respect_logic_partitioning_hints = false;
//                continue;
//            }
//            int p0 = 0, p1 = 0;
//            for (int p : {0, 1}) { // for both polarities
//                assert(decisionLevel() == d);
//                double ss = score->getSolverScore(this);
//                newDecisionLevel();
//                Lit l = mkLit(v, p);
//                // checking literal propagations
//                uncheckedEnqueue(l);
//                lbool res = laPropagateWrapper();
//                if (res == l_False) {
//                    return {laresult::la_tl_unsat, lit_Undef};
//                } else if (res == l_Undef) {
//                    cancelUntil(0);
//                    return {laresult::la_restart, lit_Undef};
//                }
//                // Else we go on
//                if (decisionLevel() == d + 1) {
//                    // literal is succesfully propagated
//                    score->updateSolverScore(ss, this);
//                } else if (decisionLevel() == d) {
//                    // propagation resulted in backtrack
//                    score->updateRound();
//                    break;
//                } else {
//                    // Backtracking should happen.
//                    return {laresult::la_unsat, lit_Undef};
//                }
//                p == 0 ? p0 = ss : p1 = ss;
//                // Update also the clause deletion heuristic?
//                cancelUntil(decisionLevel() - 1);
//            }
//            if (value(v) == l_Undef) {
//                // updating var score
//                score->setLAValue(v, p0, p1);
//                score->updateLABest(v);
//            }
//        }
//        Lit best = score->getBest();
//        if (static_cast<unsigned int>(trail.size()) == dec_vars && best == lit_Undef) {
//            // all variables are set
//            return {laresult::la_sat, best};
//        }
//
//        // lookahead phase is over
//        if (!config.sat_picky()) { idx = (idx + i) % nVars(); }
//        if (best != lit_Undef && !okToPartition(var(best))) { unadvised_splits++; }
//
//        auto end = std::chrono::steady_clock::now();
//        auto diff = end - start;
//        lookahead_time += std::chrono::duration_cast<std::chrono::milliseconds> (diff).count();
//        return {laresult::la_ok, best};
//    } else {
        auto start = std::chrono::steady_clock::now();
        Lit next = lit_Undef;

        if (next == lit_Undef) {
            switch (notifyConsistency()) {
                case ConsistencyAction::BacktrackToZero:
                    cancelUntil(0);
                    break;
                case ConsistencyAction::ReturnUndef:
                    return {laresult::la_restart, next};
                case ConsistencyAction::SkipToSearchBegin:
                case ConsistencyAction::NoOp:
                default:
                    ;
            }
            // Assumptions done and the solver is in consistent state
            // New variable decision:
            decisions++;
            next = pickBranchLit();
            // Complete Call
            if ( next == lit_Undef ) {
                TPropRes res = checkTheory(true);
                if ( res == TPropRes::Unsat )
                {
                    return {laresult::la_restart, next};
                }
                assert( res == TPropRes::Decide );

                // Otherwise we still have to make sure that
                // splitting on demand did not add any new variable
                decisions++;
                next = pickBranchLit();
            }

            if (next == lit_Undef){
                                return {laresult::la_sat, next};
            }
        }

        assert(value(next) == l_Undef);
        // Increase decision level and enqueue 'next'
        assert(value(next) == l_Undef);
//        newDecisionLevel();
        auto end = std::chrono::steady_clock::now();
        auto diff = end - start;
        // Model found:
        //        uncheckedEnqueue(next);

        vsids_time += std::chrono::duration_cast<std::chrono::milliseconds> (diff).count();
        return {laresult::la_ok, next};
//    }
}

void LookaheadSMTSolver::cancelUntil(int level) {
    assert(level >= 0);
    if (decisionLevel() > level) {
        CoreSMTSolver::cancelUntil(level);
        crossed_assumptions = std::min(crossed_assumptions, level);
    }
}