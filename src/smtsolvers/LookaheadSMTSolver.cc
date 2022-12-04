/*
 * Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Konstantin Britikov <konstantin.britikov@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

// 1. Can a single-literal propagation  cause some additional propagations(specifically I'm interested in updateRound()) -- Answer is yes. Additional propogations are caused by checkTheory.


// TODO: 2. Check out assertion error for derivations == 5. So basically the reason as I see it rn is a clause derivation for a clause, 3 elements of which are already propagated.
// TODO: And it was the thing, actually it just unwrapped another problem that the code had all along. The solution for it is to roll back and afterwards

// TODO: 3. Why there is such a big difference in checks between 5 derivations and 0 derivations
// TODO: 4. What is the differnce in checks for single for loop version of this file and file in master branch
// TODO: 5. Why the number of checks is significantly smaller during the beginning, but it incredibly grows at the end, even though the number of literal decreases. Does it mean that single-litteral test propagations just cut out a huge portion of clauses?
// TODO: 6. What is the reason of additional propagation in the checkTheory for single literal
#include "LookaheadSMTSolver.h"
#include "Proof.h"
#include<iterator> // for back_inserter

//LookaheadSMTSolver::LookaheadSMTSolver(SMTConfig& c, THandler& thandler)
//        : SimpSMTSolver(c, thandler)
//        , idx(0)
//        , score(c.lookahead_score_deep() ? (LookaheadScore*)(new LookaheadScoreDeep(assigns, c)) : (LookaheadScore*)(new LookaheadScoreClassic(assigns, c)))
//{}




void LookaheadSMTSolver::attachClause(CRef cr) {
    Clause const & c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.size() > 2) {
        watches[~c[2]].push(Watcher(cr, c[0]));
    } else {
//  TODO: figure out what goes wrong here
//        if(var(c[0])<init_vars || !initialized){
            if(!init_arr[var(~c[0])]){
                init_arr[var(~c[0])] = true;
                init_close_to_prop++;
            }
//            if(!next_arr[var(~c[0])]){
//                next_arr[var(~c[0])] = true;
//                close_to_prop++;
//            }
//        }
//        if(var(c[0])<init_vars || !initialized){
            if(!init_arr[var(~c[1])]){
                init_arr[var(~c[1])] = true;
                init_close_to_prop++;
            }
//            if(!next_arr[var(~c[1])]){
//                next_arr[var(~c[1])] = true;
//                close_to_prop++;
//            }
//        }
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
    init_arr.push(false);
    bound_arr.push(false);
    Var v = SimpSMTSolver::newVar(dvar);
    score->newVar();
    return v;
}

lbool LookaheadSMTSolver::solve_() {
    declareVarsToTheories();

    bound_prop = bound_arr.size();
    double nof_conflicts = restart_first;
    check_counter = 0;

    LALoopRes res = LALoopRes::unknown;
    for(int i = 0; i<next_arr.size(); i++){
      if(next_arr[i]){
        if(!init_arr[i]){
          init_arr[i] = true;
          init_close_to_prop++;
        }
      }
      else{
        if (init_arr[i]){
          next_arr[i] = true;
          close_to_prop++;
        }
      }
    }


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
//        printf("=================================\n");
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
            if(out_btlevel < decisionLevel()){
              reset_props = true;
            }
            cancelUntil(out_btlevel);
            assert(value(out_learnt[0]) == l_Undef);
            if (out_learnt.size() == 1) {
                CRef unitClause = ca.alloc(vec<Lit>{out_learnt[0]});
                if (logsProofForInterpolation()) {
                    proof->endChain(unitClause);
                }
                uncheckedEnqueue(out_learnt[0], unitClause);
            } else {
                CRef crd = ca.alloc(out_learnt, {true, computeGlue(out_learnt)});
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
            check_counter++;
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
    tested = false;

    vec<Lit> path;
    LANode const * curr = &n;
    LANode const * parent = n.p;
    // Collect the truth assignment.
    while (parent != curr) {
        path.push(curr->l);
        curr = parent;
        parent = curr->p;
    }
//    printf("Check counter: %d \n", check_counter);

#ifdef LADEBUG
    printf("Setting solver to the right dl %d\n", path.size());
#endif
    if(path.size() <= decisionLevel() || reset_props ){
        cancelUntil(0);
        #ifdef LADEBUG
            printf("Setting solver to the right dl %d\n", path.size());
        #endif
        close_to_prop = init_close_to_prop;
        reset_props= false;
        for(int i = 0; i<next_arr.size(); i++){
          next_arr[i] = init_arr[i];
        }
        for (int i = path.size() - 1; i >= 0; i--) {
            newDecisionLevel();
            if (value(path[i]) == l_Undef) {
    #ifdef LADEBUG
                printf("I will propagate %s%d\n", sign(path[i]) ? "-" : "", var(path[i]));
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
    } else {
      for (int i = path.size() - decisionLevel() - 1; i >= 0; i--) {
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
            close_to_prop = init_close_to_prop;
            for(int i = 0; i<next_arr.size(); i++){
              next_arr[i] = init_arr[i];
            }
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
//            if(cr == 1028){
//              printf("eq\n");
//            }



            unsigned c_size = c.size();
            Lit false_lit = ~p;

            // Try to avoid inspecting the clause:
            if (c_size > 2 and value(c[2]) == l_True) {
                *j++ = *i++;
                continue;
            }

            if (value(c[0]) == l_True or value(c[1]) == l_True) {
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
            if(c_size>2 && c[2]!=false_lit){
              watches[~c[2]].push(w);
            }
            *j++ = w;
            if (value(c[1]) == l_False) {
                if (!tested) {
                    if (next_arr[var(~c[0])]) {
                      close_to_prop--;
                    }
                    if (bound_arr[var(~c[0])]){
                      bound_prop--;
                    }
                    next_arr[var(~c[0])] = false;
                    bound_arr[var(~c[0])] = false;
                    if (next_arr[var(~c[1])]) {
                      close_to_prop--;
                    }
                    if (bound_arr[var(~c[1])]){
                      bound_prop--;
                    }
                    next_arr[var(~c[1])] = false;
                    bound_arr[var(~c[1])] = false;
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
//                        printf("Special ");
                    }
//                    printf("Enqueing: %d \n", var(first));
                    uncheckedEnqueue(first, cr);
                    fun_props++;
                }
            } else if (value(c[2]) == l_False) {
                if (!tested) {
                    if (!next_arr[var(~c[0])]) {
                        close_to_prop++;
                    }
                    if (!next_arr[var(~c[1])]) {
                        close_to_prop++;
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
//    close_to_prop = close_to_prop_trail[decisionLevel()];
//    printf("Level: %d \n", decisionLevel());
//    printf("Trail: %d \n", trail.size());
//    tested = false;
//    initialized = false;
//    initialized = true;
    if (laPropagateWrapper() == l_False) {
#ifdef LADEBUG
        printf("Already unsatisfiable at entering the lookahead loop\n");
#endif
        return {laresult::la_tl_unsat, lit_Undef};
    }
//    if(!initialized){
//        init_vars = nVars();
//    }
//    printf("Close to prop: %d \n", close_to_prop);
//    printf("Clauses: %d \n", ca.size());
//    tested = true;
//    initialized = true;
    confl_quota = prev;

    score->updateRound();
//    printf("Round: %d\n", score->getLatestRound());
    int i = 0;
    int d = decisionLevel();

    int count = 0;
    bool respect_logic_partitioning_hints = config.respect_logic_partitioning_hints();
    int skipped_vars_due_to_logic = 0;

#ifdef LADEBUG
    printf("Starting lookahead loop with %d vars\n", nVars());
#endif
    tested = true;
    assert(close_to_prop >= 0);
//    printf("Close to bound: %d \n", bound_prop);
    bound_prop = 0;
    for (int i = 0; i<bound_arr.size(); i++) {
      PTRef pt_r = theory_handler.varToTerm(i);
      bound_arr[i] = theory_handler.checkLitProp(PtAsgn(pt_r, l_False)) && theory_handler.checkLitProp(PtAsgn(pt_r, l_True));
      if(bound_arr[i]){
        bound_prop++;
      }
    }

//    initialized = true;
    int derivations = 0;
    Var oldBest, newBest;
    if(close_to_prop + bound_prop > 0){
      for (Var v(idx % nVars()); (close_to_prop!=0 || bound_prop!=0) && (close_to_prop + bound_prop > 0) && !score->isAlreadyChecked(v); v = Var((idx + (++i)) % nVars())) {
        assert(v>=0 && bound_prop>=0 && close_to_prop>=0);
        if (next_arr[v] || bound_arr[v]) {
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
              if (value(v) != l_Undef and bound_arr[v]) {
                bound_arr[v] = false;
                bound_prop--;
              }
              // It is possible that all variables are assigned here.
              // In this case it seems that we have a satisfying assignment.
              // This is in fact a debug check
              if (static_cast<unsigned int>(trail.size()) == dec_vars) {
  #ifdef LADEBUG
                printf("All vars set?\n");
  #endif

  //              check_counter++;
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
  //              printf("%d\n", i);
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
                        close_to_prop = init_close_to_prop;
                        for(int i = 0; i<next_arr.size(); i++){
                          next_arr[i] = init_arr[i];
                        }
                        return {laresult::la_restart, best};
                    }
                    // Else we go on
                    if (decisionLevel() == d + 1) {
    #ifdef LADEBUG
    //                printf(" -> Successfully propagated %d lits\n", trail.size() - tmp_trail_sz);
    #endif
                        score->updateSolverScore(ss, this);
                    } else if (decisionLevel() == d) {
    #ifdef LADEBUG
                        printf(" -> Propagation resulted in backtrack\n");
    #endif
                      derivations++;
//                      if(derivations>5 || value(best) != l_Undef){
//                          derivations=0;
                      score->updateRound();
//                        }
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
  //                  cancel_counter++;
                    cancelUntil(decisionLevel() - 1);
                }
                if (value(v) == l_Undef) {
    #ifdef LADEBUG
                    printf("Updating var %d to (%d, %d)\n", v, p0, p1);
    #endif
  //                  if(p0 > 0 && p1 > 0){
  //                    if(!next_arr[v]){
  //                      if(!bound_arr[v])
  //                        close_to_prop++;
  //                      next_arr[v] = true;
  //                    }
  //                  }
                    score->setLAValue(v, p0, p1);
                    score->updateLABest(v);
                }
            }
      }
    }
    int currVars = nVars();
    if(close_to_prop + bound_prop  <= 0){
      for(Var v(idx % nVars()); !score->isAlreadyChecked(v); v = Var((idx + (++i)) % nVars())) {
//          printf("Vars: %d \n", nVars());
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
            // It is possible that all variables are assigned here.
            // In this case it seems that we have a satisfying assignment.
            // This is in fact a debug check
            if (static_cast<unsigned int>(trail.size()) == dec_vars) {
#ifdef LADEBUG
              printf("All vars set?\n");
#endif
//              check_counter++;
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
          if(v<currVars) {
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
                  close_to_prop = init_close_to_prop;
                  for(int i = 0; i<next_arr.size(); i++){
                    next_arr[i] = init_arr[i];
                  }
                  return {laresult::la_restart, best};
                }
                // Else we go on
                if (decisionLevel() == d + 1) {
    #ifdef LADEBUG
    //                printf(" -> Successfully propagated %d lits\n", trail.size() - tmp_trail_sz);
    #endif
                score->updateSolverScore(ss, this);
              } else if (decisionLevel() == d) {
    #ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack\n");
    #endif
    //            derivations++;
    //            if(derivations>5 || value(best) != l_Undef ){
    //              derivations=0;
                  score->updateRound();
    //            }
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
    //          cancel_counter++;
              cancelUntil(decisionLevel() - 1);
            }
           }
          if (value(v) == l_Undef) {
#ifdef LADEBUG
          printf("Updating var %d to (%d, %d)\n", v, p0, p1);
#endif
            assert(p0 <= 1 and p1 <= 1);
            score->setLAValue(v, p0, p1);
            score->updateLABest(v);
            break;
          }
      }
    }
    tested = false;
    Lit best = score->getBest();
//    initialized = true;
//    printf("Best: %d\n", var(best));
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
    return {laresult::la_ok, best};
}



// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void LookaheadSMTSolver::cancelUntil(int level)
{
  if (decisionLevel() > level)
  {
    if (trail.size() > longestTrail) {
      for (auto p : trail) {
        savedPolarity[var(p)] = not sign(p);
      }
      longestTrail = trail.size();
    }
    for (int c = trail.size()-1; c >= trail_lim[level]; c--)
    {
      Var      x  = var(trail[c]);
#ifdef PEDANTIC_DEBUG
      assert(assigns[x] != l_Undef);
#endif
      assigns [x] = l_Undef;
      insertVarOrder(x);
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);

    //if ( first_model_found )
    theory_handler.backtrack(trail.size());
  }
}
