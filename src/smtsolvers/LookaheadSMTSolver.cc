/*
 * Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "LookaheadSMTSolver.h"
#include "Proof.h"

LookaheadSMTSolver::LookaheadSMTSolver(SMTConfig& c, THandler& thandler)
        : SimpSMTSolver(c, thandler)
        , idx(0)
        , score(c.lookahead_score_deep() ? (LookaheadScore*)(new LookaheadScoreDeep(assigns, c)) : (LookaheadScore*)(new LookaheadScoreClassic(assigns, c)))
{}

void LookaheadSMTSolver::attachClause(CRef cr) {
    Clause const & c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.size() > 2) {
        watches[~c[2]].push(Watcher(cr, c[0]));
    } else {
        if(!next_arr[var(~c[0])]){
            close_to_prop++;
            next_arr[var(~c[0])] = true;
        }
        if(!next_arr[var(~c[1])]){
            close_to_prop++;
            next_arr[var(~c[1])] = true;
        }
    }

    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size();
}


void LookaheadSMTSolver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    if (strict) {
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
        if (c.size() > 2)
            remove(watches[~c[2]], Watcher(cr, c[0]));
    } else {
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
        if (c.size() > 2)
            watches.smudge(~c[2]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size();
}

Var LookaheadSMTSolver::newVar(bool dvar) {
    next_arr.push(false);
    bound_arr.push(true);
    Var v = SimpSMTSolver::newVar(dvar);
    score->newVar();
    return v;
}

lbool LookaheadSMTSolver::solve_() {
    declareVarsToTheories();


    double nof_conflicts = restart_first;

    LALoopRes res = LALoopRes::unknown;

    while (res == LALoopRes::unknown || res == LALoopRes::restart) {
        //cerr << "; Doing lookahead for " << nof_conflicts << " conflicts\n";
        ConflQuota conflict_quota;
        //if (config.lookahead_restarts()) {
        //    conflict_quota = ConflQuota((int)nof_conflicts);
        //}
        res = solveLookahead();

        nof_conflicts = restartNextLimit(nof_conflicts);
    }

    if (res == LALoopRes::sat) {
        model.growTo(nVars());
        for (unsigned int i = 0; i < dec_vars; i++) {
            Var p = var(trail[i]);
            model[p] = value(p);
        }
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
lbool LookaheadSMTSolver::laPropagateWrapper()
{
    CRef cr;
    bool diff;
    do {
        diff = false;
        while ((cr = propagate()) != CRef_Undef) {
            if (decisionLevel() == 0)
                return l_False; // Unsat
            -- confl_quota;
#ifdef LADEBUG
            cerr << "; Got a conflict, quota now " << confl_quota.getQuota() << "\n";
#endif
            if (confl_quota <= 0)
                return l_Undef;

            vec<Lit> out_learnt;
            int out_btlevel;
            analyze(cr, out_learnt, out_btlevel);
#ifdef LADEBUG
            printf("Conflict: I would need to backtrack from %d to %d\n", decisionLevel(), out_btlevel);
#endif
            cancelUntil(out_btlevel);
            assert(value(out_learnt[0]) == l_Undef);
            if (out_learnt.size() == 1) {
                uncheckedEnqueue(out_learnt[0]);
            } else {
                CRef crd = ca.alloc(out_learnt, true);
                if (logsProofForInterpolation()) {
                    proof->endChain(crd);
                }
                learnts.push(crd);
                attachClause(crd);
                uncheckedEnqueue(out_learnt[0], crd);
            }
            diff = true;
        }
        if (!diff) {
            TPropRes res = checkTheory(true);
            if (res == TPropRes::Unsat) {
#ifdef LADEBUG
                printf("Theory unsatisfiability\n");
#endif
                return l_False; // Unsat
            }
            else if (res == TPropRes::Propagate) {
#ifdef LADEBUG
                printf("Theory propagation / conflict\n");
#endif
                diff = true;
                -- confl_quota;
#ifdef LADEBUG
                cerr << "; Got a theory conflict, quota now " << confl_quota.getQuota() << "\n";
#endif
                if (confl_quota <= 0)
                    return l_Undef;
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
    cancelUntil(0);

    vec<Lit> path;
    LANode const * curr = &n;
    LANode const * parent = n.p;
    // Collect the truth assignment.
    while (parent != curr) {
        path.push(curr->l);
        curr = parent;
        parent = curr->p;
    }

#ifdef LADEBUG
    printf("Setting solver to the right dl %d\n", path.size());
#endif
    for (int i = path.size() - 1; i >= 0; i--)
    {
        newDecisionLevel();

        if (value(path[i]) == l_Undef) {
#ifdef LADEBUG
            printf("I will propagate %d\n", var(path[i]));
#endif
            int curr_dl = decisionLevel();
            uncheckedEnqueue(path[i]);
            lbool res = laPropagateWrapper();
            // Here it is possible that the solver is on level 0 and in an inconsistent state.  How can I check this?
            if (res == l_False) {
                return PathBuildResult::pathbuild_tlunsat; // Indicate unsatisfiability
            } else if (res == l_Undef) {
                cancelUntil(0);
                return PathBuildResult::pathbuild_restart; // Do a restart
            }
            if (curr_dl != decisionLevel()) {
                return PathBuildResult::pathbuild_unsat;
            }
        } else {
#ifdef LADEBUG
            printf("Would propagate %s%d but the literal is already assigned\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
            if (value(path[i]) == l_False) {
#ifdef LADEBUG
                printf("Unsatisfiable branch since I'd like to propagate %s%d but %s%d is assigned already\n", sign(path[i]) ? "-" : "", var(path[i]), sign(~path[i]) ? "-" : "", var(path[i]));
                printf("Marking the subtree false:\n");
                n->print();
#endif
                return PathBuildResult::pathbuild_unsat;
            } else {
                assert(value(path[i]) == l_True);
            }
        }
    }
    return PathBuildResult::pathbuild_success;
}

LookaheadSMTSolver::laresult LookaheadSMTSolver::expandTree(LANode & n, std::unique_ptr<LANode> c1, std::unique_ptr<LANode> c2)
{
    assert(c1);
    assert(c2);
    // Do the lookahead
    assert(decisionLevel() == n.d);
    auto [res, best] = lookaheadLoop();
    assert(decisionLevel() <= n.d);
    if (res != laresult::la_ok)
        return res;

    assert(best != lit_Undef);

    c1->p = &n;
    c1->d = n.d+1;
    c1->l = best;
    c2->p = &n;
    c2->d = n.d+1;
    c2->l = ~best;
    n.c1 = std::move(c1);
    n.c2 = std::move(c2);

    return laresult::la_ok;
}
// The new try for the lookahead with backjumping:
// Do not write this as a recursive function but instead maintain the
// tree explicitly.  Each internal node should have the info whether its
// both children have been constructed and whether any of its two
// children has been shown unsatisfiable either directly or with a
// backjump.
LookaheadSMTSolver::LALoopRes LookaheadSMTSolver::solveLookahead() {
    struct PlainBuildConfig {
        static bool stopCondition(LANode &, int) { return false; }
        static LALoopRes exitState() { return LALoopRes::unknown; }
    };
    return buildAndTraverse<LANode, PlainBuildConfig>(PlainBuildConfig()).first;
};



/*_________________________________________________________________________________________________
  |
  |  propagate : [void]  ->  [Clause*]
  |
  |  Description:
  |    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
  |    otherwise NULL.
  |
  |    Post-conditions:
  |      * the propagation queue is empty, even if there was a conflict.
  |________________________________________________________________________________________________@*/
CRef LookaheadSMTSolver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()) {
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;) {
            // Try to avoid inspecting the clause:

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];



            unsigned c_size = c.size();
            Lit false_lit = ~p;

            // Try to avoid inspecting the clause:
            if (c_size > 2 and value(c[2]) == l_True) {
                if (!tested) {
                    if (next_arr[var(~c[0])]) {
                        close_to_prop--;
                        next_arr[var(~c[0])] = false;
                    }
                    if (next_arr[var(~c[1])]) {
                        close_to_prop--;
                        next_arr[var(~c[1])] = false;
                    }
                }
                *j++ = *i++;
                continue;
            }

            if (value(c[0]) == l_True or value(c[1]) == l_True) {
                if (!tested) {
                    if (next_arr[var(~c[0])]) {
                        close_to_prop--;
                    }
                    if (next_arr[var(~c[1])]) {
                        close_to_prop--;
                    }
                    next_arr[var(~c[0])] = false;
                    next_arr[var(~c[1])] = false;
                }
                *j++ = *i++;
                continue;
            }

            if (c[0] == false_lit) {
                std::swap(c[0], c[1]);
            }
            if (c_size > 2) {
                if (c[1] == false_lit) {
                    std::swap(c[1], c[2]);
                }
                if (value(c[0]) == l_False) {
                    std::swap(c[0], c[1]);
                }
            }
            assert((c_size == 2 and c[1] == false_lit) or (c[2] == false_lit or (c[1] == false_lit and value(c[2]) == l_False)));
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            Watcher w = Watcher(cr, first);
            // Look for new watch:
            for (unsigned k = 3; k < c_size; k++) {
                if (value(c[k]) != l_False) {
                    assert(c[2] == false_lit);
                    std::swap(c[2], c[k]);
                    watches[~c[2]].push(w);
                    goto NextClause;
                }
            }

            *j++ = w;
            if (value(c[1]) == l_False) {
                if (!tested) {
                    if (next_arr[var(~c[0])]) {
                        close_to_prop--;
                    }
                    if (next_arr[var(~c[1])]) {
                        close_to_prop--;
                    }
                    next_arr[var(~c[0])] = false;
                    next_arr[var(~c[1])] = false;
                }
                if (value(first) == l_False) {
                    // clause is falsified
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end) {
                        *j++ = *i++;
                    }
                    if (decisionLevel() == 0 && this->logsProofForInterpolation()) {
                        this->finalizeProof(confl);
                    }
                } else {  // clause is unit under assignment:
                    if (decisionLevel() == 0 && this->logsProofForInterpolation()) {
                        // MB: we need to log the derivation of the unit clauses at level 0, otherwise the proof
                        //     is not constructed correctly
                        proof->beginChain(cr);

                        for (unsigned k = 1; k < c_size; k++) {
                            assert(level(var(c[k])) == 0);
                            assert(reason(var(c[k])) != CRef_Fake);
                            assert(reason(var(c[k])) != CRef_Undef);
                            proof->addResolutionStep(reason(var(c[k])), var(c[k]));
                        }
                        CRef unitClause = ca.alloc(vec<Lit>{first});
                        proof->endChain(unitClause);
                        // Replace the reason for enqueing the literal with the unit clause.
                        // Necessary for correct functioning of proof logging in analyze()
                        cr = unitClause;
                    }
                    uncheckedEnqueue(first, cr);
                    fun_props++;
                }
            } else if (value(c[2]) == l_False) {
                if (!tested) {
                    if (!next_arr[var(~c[0])]) {
                        close_to_prop ++;
                    }
                    if (!next_arr[var(~c[1])]) {
                        close_to_prop ++;
                    }
                    next_arr[var(~c[0])] = true;
                    next_arr[var(~c[1])] = true;
                }
            }
            NextClause:
            ;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

std::pair<LookaheadSMTSolver::laresult,Lit> LookaheadSMTSolver::lookaheadLoop() {
    ConflQuota prev = confl_quota;
    confl_quota = ConflQuota(); // Unlimited;
    if (laPropagateWrapper() == l_False) {
#ifdef LADEBUG
        printf("Already unsatisfiable at entering the lookahead loop\n");
#endif
        return {laresult::la_tl_unsat, lit_Undef};
    }
    confl_quota = prev;

    score->updateRound();
    int i = 0;
    int d = decisionLevel();

    int count = 0;
    bool respect_logic_partitioning_hints = config.respect_logic_partitioning_hints();
    int skipped_vars_due_to_logic = 0;

#ifdef LADEBUG
    printf("Starting lookahead loop with %d vars\n", nVars());
#endif
    tested = true;
    for (Var v(idx % nVars()); !score->isAlreadyChecked(v); v = Var((idx + (++i)) % nVars())) {
          if (next_arr[v] || close_to_prop == 0) {
              if (!decision[v]) {
                  score->setChecked(v);
  #ifdef LADEBUG
                  cout << "Not a decision variable: " << v << "("
                       << theory_handler.getLogic().printTerm(theory_handler.varToTerm(v)) << ")\n";
  #endif
                  continue;
              }
              if (v == (idx * nVars()) && skipped_vars_due_to_logic > 0) {
                  respect_logic_partitioning_hints = false; // Allow branching on these since we looped back.
              }
              if (respect_logic_partitioning_hints && !okToPartition(v)) {
                  skipped_vars_due_to_logic++;
                  std::cout << "Skipping " << v << " since logic says it's not good\n";
                  continue; // Skip the vars that the logic considers bad to split on
              }

  #ifdef LADEBUG
                  printf("Checking var %d\n", v);
  #endif
              Lit best = score->getBest();
              if (value(v) != l_Undef or (best != lit_Undef and score->safeToSkip(v, best))) {
  #ifdef LADEBUG
                  printf("  Var is safe to skip due to %s\n",
                         value(v) != l_Undef ? "being assigned" : "having low upper bound");
  #endif
                  if (value(v) != l_Undef and next_arr[v]) {
                      next_arr[v] = false;
                      close_to_prop--;
                  }
                  // It is possible that all variables are assigned here.
                  // In this case it seems that we have a satisfying assignment.
                  // This is in fact a debug check
                  if (static_cast<unsigned int>(trail.size()) == dec_vars) {
  #ifdef LADEBUG
                      printf("All vars set?\n");
  #endif

                      if (checkTheory(true) != TPropRes::Decide)
                          return {laresult::la_tl_unsat, best}; // Problem is trivially unsat
                      assert(checkTheory(true) == TPropRes::Decide);
  #ifndef NDEBUG
                      for (int j = 0; j < clauses.size(); j++) {
                          Clause &c = ca[clauses[j]];
                          unsigned k;
                          for (k = 0; k < c.size(); k++) {
                              if (value(c[k]) == l_True) {
                                  break;
                              }
                          }
                          assert(k < c.size());
                      }
  #endif
                      best = lit_Undef;
                      return {laresult::la_sat, best}; // Stands for SAT
                  }
                  continue;
              }
              if (trail.size() == nVars() + skipped_vars_due_to_logic) {
                  std::cout << "; " << skipped_vars_due_to_logic << " vars were skipped\n";
                  respect_logic_partitioning_hints = false;
                  continue;
              }
              count++;
              int p0 = 0, p1 = 0;
              for (int polarity : {0, 1}) {
                  // do for both polarities
                  assert(decisionLevel() == d);
                  double ss = score->getSolverScore(this);
                  newDecisionLevel();
                  Lit l = mkLit(v, polarity);
                  fun_props = 1;


  #ifdef LADEBUG
                  printf("Checking lit %s%d\n", p == 0 ? "" : "-", v);
  #endif
                  uncheckedEnqueue(l);
                  lbool res = laPropagateWrapper();
                  if (res == l_False) {
                      best = lit_Undef;
                      return {laresult::la_tl_unsat, best};
                  } else if (res == l_Undef) {
                      cancelUntil(0);
                      return {laresult::la_restart, best};
                  }
                  // Else we go on
                  if (decisionLevel() == d + 1) {
  #ifdef LADEBUG
  //                printf(" -> Successfully propagated %d lits\n", trail.size() - tmp_trail_sz);
  #endif
                      score->updateSolverScore(ss, this);
  //                    if (!rest){
  //                        if(ss - fun_props != 0){
  //                            printf("Strange\n");
  //                        }
  //                    }
                  } else if (decisionLevel() == d) {
  #ifdef LADEBUG
                      printf(" -> Propagation resulted in backtrack\n");
  #endif
                      score->updateRound();
                      break;
                  } else {
  #ifdef LADEBUG
                      printf(" -> Propagation resulted in backtrack: %d -> %d\n", d, decisionLevel());
  #endif
                      // Backtracking should happen.
                      best = lit_Undef;
                      return {laresult::la_unsat, best};
                  }
                  polarity == 0 ? p0 = ss : p1 = ss;
                  // Update also the clause deletion heuristic?
                  cancelUntil(decisionLevel() - 1);
              }
              if (value(v) == l_Undef) {
  #ifdef LADEBUG
                  printf("Updating var %d to (%d, %d)\n", v, p0, p1);
  #endif
                  if(p0 > 0 && p1 > 0){
                    if(!next_arr[v]){
                      close_to_prop++;
                      next_arr[v] = true;
                    }
                  }
                  score->setLAValue(v, p0, p1);
                  score->updateLABest(v);
              }
          }
      }

    tested = false;
    best = score->getBest();
    if (static_cast<unsigned int>(trail.size()) == dec_vars and best == lit_Undef) {
#ifdef LADEBUG
        printf("All variables are already set, so we have nothing to branch on and this is a SAT answer\n");
#endif
        return {laresult::la_sat, best};
    }
    assert(best != lit_Undef);
#ifdef LADEBUG
    printf("Lookahead phase over successfully\n");
//    printf("Best I found propagates high %d and low %d\n",
//           LAexacts[var(best)].getEx_h(),
//           LAexacts[var(best)].getEx_l());
#endif
    idx = (idx + i) % nVars();
    if (!okToPartition(var(best))) {
        unadvised_splits++;
    }
    return laresult::la_ok;
}
