/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ScatterSplitter.h"
#include "Proof.h"
#include "SystemQueries.h"
#include "ReportUtils.h"

#include "SystemQueries.h"
#include "ReportUtils.h"

namespace opensmt
{
    extern bool stop;
}

ScatterSplitter::ScatterSplitter(SMTConfig & c, THandler & t)
    : SimpSMTSolver         (c, t)
    , splitConfig           (config)
{}

bool ScatterSplitter::branchLitRandom() {
    return ((not splitConfig.splitOn() and drand(random_seed) < random_var_freq) or
            (splitConfig.splitOn() and splitConfig.preferRandom()))
           and not order_heap.empty();
}

Var ScatterSplitter::doActivityDecision() {
    vec<int> discarded;
    Var next = var_Undef;
    while (next == var_Undef || value(next) != l_Undef || !decision[next]) {
        if (order_heap.empty()) {
            if (splitConfig.preferTerm() or splitConfig.preferFormula()) {
                if (discarded.size() > 0) {
                    next = discarded[0];
                } else {
                    next = var_Undef;
                }
            } else {
                next = var_Undef;
            }
            break;
        } else {
            next = order_heap.removeMin();
            if (splitConfig.splitOn() and next != var_Undef) {
                if (splitConfig.preferTerm() and not theory_handler.isDeclared(next)) {
                    discarded.push(next);
                    next = var_Undef;
                } else if (splitConfig.preferFormula() and theory_handler.isDeclared(next)) {
                    discarded.push(next);
                    next = var_Undef;
                }
            }
        }
    }
    if (splitConfig.preferTerm() or splitConfig.preferFormula())
        for (Var v : discarded)
            order_heap.insert(v);

    return next;
}

bool ScatterSplitter::okContinue() const {
    if (!CoreSMTSolver::okContinue()) {
        return false;
    }
    if (conflicts % 1000 == 0 and splitConfig.resourceLimitReached(decisions)) {
        opensmt::stop = true;
        return false;
    }
    return true;
}

void ScatterSplitter::runPeriodics() {
    if (conflicts % 1000 == 0)
        clausesPublish();

    if (decisionLevel() == 0) {
        if (conflicts > conflicts_last_update + 1000) {
            clausesUpdate();
            conflicts_last_update = conflicts;
        }
    }
}

/*_________________________________________________________________________________________________
  |
  |  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
  |
  |  Description:
  |    Search for a model the specified number of conflicts, keeping the number of learnt clauses
  |    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
  |    indicate infinity.
  |
  |  Output:
  |    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
  |    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
  |    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
  |________________________________________________________________________________________________@*/
lbool ScatterSplitter::search(int nof_conflicts, int nof_learnts)
{
// Time my execution to search_timer
//    opensmt::StopWatch stopwatch = opensmt::StopWatch(search_timer);
#ifdef VERBOSE_SAT
    cerr << "Units when starting search:" << endl;
    for (int i = 2; i < trail.size(); i++)
    {
        char* name;
        theory_handler.getVarName(var(trail[i]), &name);
        cerr << (sign(trail[i]) ? "not " : "");
        cerr << name << endl;
        ::free(name);
    }
#endif
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

#ifdef STATISTICS
    const double start = cpuTime( );
#endif
    // (Incomplete) Check of Level-0 atoms

    TPropRes res = checkTheory(false, conflictC);
    if ( res == TPropRes::Unsat) {
        return zeroLevelConflictHandler();
    }

    assert( res == TPropRes::Decide || res == TPropRes::Propagate ); // Either good for decision (from TSolver's perspective) or propagate
#ifdef STATISTICS
    tsolvers_time += cpuTime( ) - start;
#endif

    //
    // Decrease activity for booleans
    //
//    boolVarDecActivity( );

#ifdef PEDANTIC_DEBUG
    bool thr_backtrack = false;
#endif
    assert(splitConfig.isSplitTypeScatter());
    while (static_cast<int>(splits.size()) < splitConfig.splitTargetNumber() - 1) {
        if (!okContinue())
            return l_Undef;
        runPeriodics();

        CRef confl = propagate();
        if (confl != CRef_Undef) {
            // CONFLICT
            conflicts++;
            conflictC++;
            if (decisionLevel() == 0) {
                return zeroLevelConflictHandler();
            }
            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);

            cancelUntil(backtrack_level);

            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1) {
                CRef reason = CRef_Undef;
                if (logsProofForInterpolation()) {
                    CRef cr = ca.alloc(learnt_clause, false);
                    proof->endChain(cr);
                    reason = cr;
                }
                uncheckedEnqueue(learnt_clause[0], reason);
            } else {
                // ADDED FOR NEW MINIMIZATION
                learnts_size += learnt_clause.size( );
                all_learnts ++;

                CRef cr = ca.alloc(learnt_clause, true);

                if (logsProofForInterpolation()) {
                    proof->endChain(cr);
                }
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            learntSizeAdjust();
        } else {
            // NO CONFLICT
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) or not withinBudget()) {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) {
                return zeroLevelConflictHandler();
            }
            // Two ways of reducing the clause.  The latter one seems to be working
            // better (not running proper tests since the cluster is down...)
            // if ((learnts.size()-nAssigns()) >= max_learnts)
            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts) {
                // Reduce the set of learnt clauses:
                reduceDB();
            }

            // Early Pruning Call
            // Step 1: check if the current assignment is theory-consistent

            TPropRes res = checkTheory(false, conflictC);
            if (res == TPropRes::Unsat) {
                return zeroLevelConflictHandler();
            } else if (res == TPropRes::Propagate) {
                continue; // Theory conflict: time for bcp
            } else if (res == TPropRes::Decide) {
                ; // Sat and no deductions: go ahead
            } else {
                assert( false );
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True) {
                    // Dummy decision level:
                    newDecisionLevel();
                } else if (value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    int max = 0;
                    for (Lit q : conflict) {
                        if (!sign(q)) {
                            max = assumptions_order[var(q)] > max ? assumptions_order[var(q)] : max;
                        }
                    }
                    conflict_frame = max+1;
                    return zeroLevelConflictHandler();
                } else {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef) {
                // Assumptions done and the solver is in consistent state
                updateSplitState();
                if (not splitConfig.splitStarted() and splitConfig.splitOn() and scatterLevel()) {
                    if (!createSplit_scatter()) { // Rest is unsat
                        opensmt::stop = true;
                        return l_Undef;
                    } else {
                        continue;
                    }
                }
                // Otherwise continue to variable decision.


                // New variable decision:
                decisions++;
                next = pickBranchLit();
#ifdef VERBOSE_SAT
                char* name;
                if (next != lit_Undef) {
                    theory_handler.getVarName(var(next), &name);
                    cerr << "branch: " << toInt(next) << (sign(next) ? " not " : " ") << name << endl;
                    ::free(name);
                }
                else cerr << "branch: " << toInt(next) << (sign(next) ? " not " : " ") << "undef" << endl;

#endif
                // Complete Call
                if (next == lit_Undef) {
#ifdef STATISTICS
                    const double start = cpuTime( );
#endif
                    res = checkTheory(true, conflictC);
#ifdef STATISTICS
                    tsolvers_time += cpuTime( ) - start;
#endif
                    if ( res == TPropRes::Propagate ) {
                        continue;
                    }
                    if ( res == TPropRes::Unsat ) {
                        return zeroLevelConflictHandler();
                    }
                    assert( res == TPropRes::Decide );

                    // Otherwise we still have to make sure that
                    // splitting on demand did not add any new variable
                    decisions++;
                    next = pickBranchLit();
                }

                if (next == lit_Undef) {
                    // Model found:
                    return l_True;
                }
            }
            assert(value(next) == l_Undef);
            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
    cancelUntil(0);
    createSplit_scatter();
    opensmt::stop = true;
    return l_Undef;
}

lbool ScatterSplitter::solve_() {
//    opensmt::PrintStopWatch watch("solve time", cerr);

    for (Lit l : this->assumptions) {
        this->addVar_(var(l));
    }
    this->clausesUpdate();

    // Inform theories of the variables that are actually seen by the
    // SAT solver.
    declareVarsToTheories();

    assert(config.sat_split_type() == spt_scatter);

    splitConfig.reset(decisions);

    if (config.dump_only()) {
        return l_Undef;
    }

    random_seed = config.getRandomSeed();

    if (config.sat_dump_cnf != 0) {
        dumpCNF();
    }

    model.clear();
    conflict.clear();

    if (!ok) {
        return l_False;
    }

    solves++;

    double  nof_conflicts     = restart_first;
    double  nof_learnts       = nClauses() * learntsize_factor;
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    unsigned last_luby_k = luby_k;

    if (verbosity >= 1) {
        fprintf(stderr, "; ============================[ Search Statistics ]==============================\n");
        fprintf(stderr, "; | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        fprintf(stderr, "; |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        fprintf(stderr, "; ===============================================================================\n");
    }
    double next_printout = restart_first;

    // Search:

    if (config.dryrun()) {
        stop = true;
    }
    while (status == l_Undef && !opensmt::stop && !this->stop) {
        // Print some information. At every restart for
        // standard mode or any 2^n intervarls for luby
        // restarts
        if (conflicts == 0 || conflicts >= next_printout) {
            if (config.verbosity() > 0) {
                reportf("; %9d | %8d %8d | %8.3f s | %6.3f MB\n", (int) conflicts, (int) learnts.size(), nLearnts(),
                        cpuTime(), memUsed() / 1048576.0);
                fflush(stderr);
            }
        }

        if (config.sat_use_luby_restart) {
            next_printout *= 2;
        } else {
            next_printout *= restart_inc;
        }
        // XXX
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts = restartNextLimit( nof_conflicts );
        if (config.sat_use_luby_restart) {
            if (last_luby_k != luby_k) {
                nof_learnts *= 1.215;
            }
            last_luby_k = luby_k;
        } else {
            nof_learnts *= learntsize_inc;
        }
    }

    if (status == l_True) {
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) {
            model[i] = value(i);
        }
    } else {
        assert( opensmt::stop || status == l_False || this->stop);
    }

    // We terminate
    return status;
}

lbool ScatterSplitter::zeroLevelConflictHandler() {
    if (splits.empty()) {
        opensmt::stop = true;
        return l_Undef;
    } else {
        return CoreSMTSolver::zeroLevelConflictHandler();
    }
}

bool ScatterSplitter::scatterLevel() {
    int d;
    if (not splitConfig.splitOn()) {
        return false;
    }
    // Current scattered instance number i = splits.size() + 1
    float r = 1/(float)(splitConfig.splitTargetNumber()-splits.size());
    for (int i = 0; ; i++) {
        // 2 << i == 2^(i+1)
        if ((2 << (i-1) <= splitConfig.splitTargetNumber() - static_cast<int>(splits.size())) &&
            (2 << i >= splitConfig.splitTargetNumber() - static_cast<int>(splits.size()))) {
            // r-1(2^i) < 0 and we want absolute
            d = -(r-1/(float)(2<<(i-1))) > r-1/(float)(2<<i) ? i+1 : i;
            break;
        }
    }
    return d == decisionLevel() - assumptions.size();
}

bool ScatterSplitter::createSplit_scatter() {
    assert(splits.size() == split_assumptions.size());
    SplitData splitData;
    vec<Lit> constraints_negated;
    vec<Lit>& split_assumption = split_assumptions.back();
    // Add the literals on the decision levels
    for (int i = assumptions.size(); i < decisionLevel(); i++) {
        Lit l = trail[trail_lim[i]];
        splitData.addConstraint<vec<Lit>>({l});
        // Remember this literal in the split assumptions vector of the
        // SAT solver
        split_assumption.push(l);
        // This will be added to the SAT formula to exclude the search
        // space
        constraints_negated.push(~l);
    }
    for (size_t i = 0; i < split_assumptions.size()-1; i++) {
        vec<Lit> tmp;
        for (auto tr : split_assumptions[i]) {
            tmp.push(~tr);
        }
        splitData.addConstraint(tmp);
    }

    cancelUntil(0);
    if (!excludeAssumptions(constraints_negated))
        return false;
    assert(ok);
    splitConfig.startSplit();
    splitConfig.continueSplit();
    splitConfig.updateNextSplitLimit(decisions);

    splits.emplace_back(std::move(splitData));

    return true;
}

bool ScatterSplitter::excludeAssumptions(vec<Lit> const & neg_constrs) {
    addOriginalClause(neg_constrs);
    simplify();
    return ok;
}

void ScatterSplitter::updateSplitState() {
    if (splitConfig.splitStarted() and splitConfig.splitLimitReached(decisions)) {
        cancelUntil(0);
        splitConfig.unStartSplit();
        splitConfig.continueSplit();
        splitConfig.updateNextSplitLimit(decisions);
    }
}