//
// Created by prova on 07.02.19.
//

#include "LookaheadSMTSolver.h"

LookaheadSMTSolver::LookaheadSMTSolver(SMTConfig& c, THandler& thandler)
	: SimpSMTSolver(c, thandler)
    , la_tl_unsat           (laresult::tl_unsat)
    , la_sat                (laresult::sat)
    , la_restart            (laresult::restart)
    , la_unsat              (laresult::unsat)
    , la_ok                 (laresult::ok)
    , latest_round          (0)
    , buf_LABests           (c.randomize_lookahead_bufsz(), assigns, c.randomize_lookahead(), c.getRandomSeed())
{}

Var LookaheadSMTSolver::newVar(bool sign, bool dvar)
{
    Var v = SimpSMTSolver::newVar(sign, dvar);
    LAupperbounds.push(); // leave space for the var
    LAexacts.push();      // leave space for the var
    return v;
}

const LookaheadSMTSolver::UBel LookaheadSMTSolver::UBel_Undef(-1, -1);

// safeToSkip: given an exact value e for a variable b, is it safe to
// skip checking my literal's extra value in the lookahead heuristic?
//
bool LookaheadSMTSolver::UBVal::safeToSkip(const ExVal& e) const
{
    // My value needs to be current with respect to both polarities and
    // the timestamp of e
    if (!current(e)) return false;

    const UBel& ub_l = getLow();
    const UBel& ub_h = getHigh();

    assert(ub_l != UBel_Undef);

    // If my low-polarity upper bound is less than the low exact of b there is
    // no reason to check me
    if (ub_l.ub < e.getEx_l())
    {
        return true;
    }

    // If my low-polarity upper bound is equal to the low exact of b and
    // my high-polarity upper bound is less than or equal to the high
    // exact of b there is no reason to check me
    if (ub_l.ub ==  e.getEx_l() && ub_h.ub <= e.getEx_h())
    {
        return true;
    }

    // In all other cases the value needs to be checked.
    return false;
}

lbool LookaheadSMTSolver::solve_()
{
    int d;
    if (config.sat_split_type() == spt_lookahead) {
        if (config.sat_split_fixvars() > 0)
            d = config.sat_split_fixvars();
		d = getLog2Ceil(config.sat_split_num());
    }
    else {
        d = -1;
    }

    declareVarsToTheories();

    double nof_conflicts = restart_first;
    const size_t old_conflicts = nLearnts();

    int idx = 0;
//    bool first_model_found_prev = first_model_found;
//    first_model_found = true;
    LALoopRes res = LALoopRes::unknown;
    while (res == LALoopRes::unknown || res == LALoopRes::restart) {
        //cerr << "; Doing lookahead for " << nof_conflicts << " conflicts\n";
        ConflQuota conflict_quota;
        if (false) { //if (config.lookahead_restarts()) {
            conflict_quota = ConflQuota((int)nof_conflicts);
        }
        res = solveLookahead(d, idx, conflict_quota);

        nof_conflicts = restartNextLimit(nof_conflicts);
    }
//    first_model_found = first_model_found_prev;
    if (res == LALoopRes::sat)
    {
        model.growTo(nVars());
        for (int i = 0; i < dec_vars; i++) // TODO: Fix this at some point
            model[i] = value(trail[i]);
    }
    if (res == LALoopRes::unsat)
        splits.clear();
    // Without these I get a segfault from theory solver's destructor...
    cancelUntil(0);
    theory_handler.backtrack(0);
    if (res == LALoopRes::unknown || res == LALoopRes::splits)
        return l_Undef;
    if (res == LALoopRes::sat)
        return l_True;
    if (res == LALoopRes::unsat)
        return l_False;
    assert(false);
    return l_Undef;
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

lbool LookaheadSMTSolver::LApropagate_wrapper(ConflQuota& confl_quota)
{
    CRef cr;
    bool diff;
    do
    {
        diff = false;
        while ((cr = propagate()) != CRef_Undef)
        {
            if (decisionLevel() == 0)
                return l_False; // Unsat
            -- confl_quota;
#ifdef LADEBUG
            cerr << "; Got a conflict, quota now " << confl_quota << "\n";
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
            if (out_learnt.size() == 1)
            {
                uncheckedEnqueue(out_learnt[0]);
            }
            else
            {
                CRef crd = ca.alloc(out_learnt, true);
                learnts.push(crd);
                attachClause(crd);
                uncheckedEnqueue(out_learnt[0], crd);

            }
            diff = true;
        }
        if (!diff)
        {
            TPropRes res = checkTheory(true);
            if (res == TPropRes::Unsat)
            {
#ifdef LADEBUG
                printf("Theory unsatisfiability\n");
#endif
                return l_False; // Unsat
            }
            else if (res == TPropRes::Propagate)
            {
#ifdef LADEBUG
                printf("Theory propagation / conflict\n");
#endif
                diff = true;
                -- confl_quota;
#ifdef LADEBUG
                cerr << "; Got a theory conflict, quota now " << confl_quota << "\n";
#endif
                if (confl_quota <= 0)
                    return l_Undef;
            }
        }
    } while (diff);

    return l_True;
}

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
// parameter idx store where we were last time in checking the variables
// confl_quota is the maximum number of conflicts that we're allowed to collect before a restart
//
LookaheadSMTSolver::LALoopRes LookaheadSMTSolver::solveLookahead(int d, int &idx, ConflQuota confl_quota)
{
    int la_split_count = 0;

    updateRound();
    vec<LANode*> queue;
    LANode* root = new LANode();
    root->p  = root;
    queue.push(root);

    while (queue.size() != 0)
    {
//        printf("LA split count %d\n", la_split_count++);
        LANode& n = *queue.last();
        queue.pop();
#ifdef LADEBUG
        printf("main loop: dl %d -> %d\n", decisionLevel(), 0);
#endif
        cancelUntil(0);

        if (n.v == l_False)
            continue;

        vec<Lit> path;
        LANode *curr = &n;
        LANode* parent = n.p;
        // Collect the truth assignment.
        while (parent != curr)
        {
            path.push(curr->l);
            curr = parent;
            parent = curr->p;
        }

        int i;
#ifdef LADEBUG
        printf("Setting solver to the right dl %d\n", path.size());
#endif
        for (i = path.size() - 1; i >= 0; i--)
        {
            newDecisionLevel();
            if (value(path[i]) == l_Undef)
            {
#ifdef LADEBUG
                printf("I will propagate %s%d\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
                int curr_dl = decisionLevel();
                uncheckedEnqueue(path[i]);
                lbool res = LApropagate_wrapper(confl_quota);
                // Here it is possible that the solver is on level 0 and in an inconsistent state.  How can I check this?
                if (res == l_False) {
                    return LALoopRes::unsat; // Indicate unsatisfiability
                }
                else if (res == l_Undef) {
                    cancelUntil(0);
                    return LALoopRes::restart; // Do a restart
                }
                if (curr_dl != decisionLevel())
                {

//                    cerr << " -> Path this far is unsatisfiable already\n";
//                    cerr << "Marking the subtree false:\n";
//                    n.print();

                    n.v = l_False;
                    break;
                }
            }
            else
            {
#ifdef LADEBUG
                printf("Would propagate %s%d but the literal is already assigned\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
                if (value(path[i]) == l_False)
                {
                    n.v = l_False;
#ifdef LADEBUG
                    printf("Unsatisfiable branch since I'd like to propagate %s%d but %s%d is assigned already\n", sign(path[i]) ? "-" : "", var(path[i]), sign(~path[i]) ? "-" : "", var(path[i]));
                    printf("Marking the subtree false:\n");
                    n.print();
#endif
                    break;
                }
                else
                {
                    assert(value(path[i]) == l_True);
                }
            }
        }

        if (i != -1)
        {
#ifdef LADEBUG
            printf("Unsatisfiability detected on branch\n");
#endif
            continue;
        }
        if ((d >= 0) && n.d == d)
        {
#ifdef LADEBUG
            printf("Producing a split:\n");;
            printTrace();
#endif
            createSplit_lookahead();
            if (config.sat_split_test_cube_and_conquer())
                return LALoopRes::unsat; // The cube-and-conquer experiment
            else
                continue;
        }

        // Otherwise we will continue here by attempting to create two children for this node

        // Do the lookahead
        assert(decisionLevel() == n.d);
        Lit best;
        laresult res = lookahead_loop(best, idx, confl_quota);
        assert(decisionLevel() <= n.d);

        if (res == la_tl_unsat) {
            return LALoopRes::unsat;
        }
        else if (res == la_restart) {
            return LALoopRes::restart;
        }
        else if (res == la_unsat)
        {
            assert(decisionLevel() < n.d);
#ifdef LADEBUG
            printf("Unsatisfiability detected after lookahead\n");
#endif
            // level and force a backjump.  It means that the node from
            // which backjump happens is unsatisfiable.  It does not
            // mean that the path leading to the lookahead node would be
            // unsatisfiable.  Hence we need to put this node back to
            // the search queue.
            queue.push(&n);
            continue;
        }
        else if (res == la_sat)
        {
#ifdef LADEBUG
            printf("Lookahead claims to have found a satisfying truth assignment:\n");
            printTrail();
#endif
            return LALoopRes::sat;
        }
        assert(res == la_ok);
        assert(best != lit_Undef);

        LANode* c1 = new LANode(&n, best, l_Undef, n.d+1);
        LANode* c2 = new LANode(&n, ~best, l_Undef, n.d+1);

        queue.push(c1);
        queue.push(c2);

        // These are for debugging
        n.c1 = c1;
        n.c2 = c2;
    }
#ifdef LADEBUG
    root->print();
#endif
    if (d > 0)
        return LALoopRes::splits;
    return LALoopRes::unknown;
}

LookaheadSMTSolver::laresult LookaheadSMTSolver::lookahead_loop(Lit& best, int &idx, ConflQuota &confl_quota)
{
    ConflQuota unlimited;
    if (LApropagate_wrapper(unlimited) == l_False)
    {
#ifdef LADEBUG
        printf("Already unsatisfiable at entering the lookahead loop\n");
#endif
        return la_tl_unsat;
    }

    updateRound();
    int i = 0;
    int d = decisionLevel();

    int count = 0;
    bool respect_logic_partitioning_hints = config.respect_logic_partitioning_hints();
    int skipped_vars_due_to_logic = 0;

#ifdef LADEBUG
    printf("Starting lookahead loop with %d vars\n", nVars());
#endif
    for (Var v(idx % nVars()); (LAexacts[v].getRound() != latest_round); v = Var((idx + (++i)) % nVars()))
    {
        if (!decision[v]) {
            LAexacts[v].setRound(latest_round);
#ifdef LADEBUG
            printf("Not a decision variable: %d (%s)\n", v, theory_handler.getLogic().printTerm(theory_handler.varToTerm(v)));
#endif
            continue; // Skip the non-decision vars
        }
        if (v == (idx * nVars()) && skipped_vars_due_to_logic > 0)
            respect_logic_partitioning_hints = false; // Allow branching on these since we looped back.
        if (respect_logic_partitioning_hints && !(theory_handler.getLogic().okToPartition(theory_handler.varToTerm(v)))) {
            skipped_vars_due_to_logic ++;
            printf("Skipping %d since logic says it's not good\n", v);
            continue; // Skip the vars that the logic considers bad to split on
        }
#ifdef LADEBUG
        printf("Checking var %d\n", v);
#endif
        Lit best = buf_LABests.getLit();
        if (value(v) != l_Undef || (best != lit_Undef && LAupperbounds[v].safeToSkip(LAexacts[var(best)])))
        {
#ifdef LADEBUG
            printf("  Var is safe to skip due to %s\n",
                   value(v) != l_Undef ? "being assigned" : "having low upper bound");
//            if (value(v) == l_Undef)
//                printf("  Var is safe to skip due to having low upper bound\n");
#endif
            LAexacts[v].setRound(latest_round);
            // It is possible that all variables are assigned here.
            // In this case it seems that we have a satisfying assignment.
            // This is in fact a debug check
            if (trail.size() == dec_vars)
            {
#ifdef LADEBUG
                printf("All vars set?\n");
#endif
                if (checkTheory(true) != TPropRes::Decide) // TODO could also be tpr_Propagate
                    return la_tl_unsat; // Problem is trivially unsat
                assert(checkTheory(true) == TPropRes::Decide);
#ifdef LADEBUG
                for (int j = 0; j < clauses.size(); j++)
                {
                    Clause& c = ca[clauses[j]];
                    int k;
                    for (k = 0; k < c.size(); k++)
                    {
                        if (value(c[k]) == l_True)
                        {
                            break;
                        }
                    }
                    assert(k < c.size());
                }
#endif
                best = lit_Undef;
                return la_sat; // Stands for SAT
            }
            continue;
        }
        if (trail.size() == nVars() + skipped_vars_due_to_logic) {
            printf("; %d vars were skipped\n", skipped_vars_due_to_logic);
            respect_logic_partitioning_hints = false;
            continue;
        }
        count++;
        int p0 = 0, p1 = 0;
        for (int p = 0; p < 2; p++)   // do for both polarities
        {
            assert(decisionLevel() == d);
            newDecisionLevel();
            Lit l = mkLit(v, p);
            int tmp_trail_sz = trail.size();
#ifdef LADEBUG
           printf("Checking lit %s%d\n", p == 0 ? "" : "-", v);
#endif
            uncheckedEnqueue(l);
            lbool res = LApropagate_wrapper(confl_quota);
            if (res == l_False)
            {
                best = lit_Undef;
                return la_tl_unsat;
            }
            else if (res == l_Undef)
            {
                cancelUntil(0);
                return la_restart;
            }
            // Else we go on
            if (decisionLevel() == d+1)
            {
#ifdef LADEBUG
                printf(" -> Successfully propagated %d lits\n", trail.size() - tmp_trail_sz);
#endif
                for (int j = 0; j < trail.size(); j++)
                    updateLAUB(trail[j], trail.size());
            }
            else if (decisionLevel() == d)
            {
#ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack\n");
#endif
                updateRound();
                break;
            }
            else
            {
#ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack: %d -> %d\n", d, decisionLevel());
#endif
                // Backtracking should happen.
                best = lit_Undef;
                return la_restart;
            }
            p == 0 ? p0 = trail.size() : p1 = trail.size();
            // Update also the clause deletion heuristic?
            cancelUntil(decisionLevel() - 1);
        }
        if (value(v) == l_Undef)
        {
#ifdef LADEBUG
           printf("Updating var %d to (%d, %d)\n", v, p0, p1);
#endif
            setLAExact(v, p0, p1);
            updateLABest(v);
            assert(value(buf_LABests.getLit()) == l_Undef);
        }
    }
    if (trail.size() == dec_vars && buf_LABests.getLit() == lit_Undef)
    {
#ifdef LADEBUG
        printf("All variables are already set, so we have nothing to branch on and this is a SAT answer\n");
#endif
        return la_sat;
    }
    best = buf_LABests.getLit();
    assert(best != lit_Undef);
#ifdef LADEBUG
    printf("Lookahead phase over successfully\n");
    printf("Best I found propagates high %d and low %d\n",
           LAexacts[var(best)].getEx_h(),
           LAexacts[var(best)].getEx_l());
#endif
    idx = (idx + i) % nVars();
    if (!theory_handler.getLogic().okToPartition(theory_handler.varToTerm(var(best)))) { unadvised_splits++; }
    return la_ok;
}

void LookaheadSMTSolver::updateLABest(Var v)
{
    assert(value(v) == l_Undef);
    ExVal& e = LAexacts[v];
    Lit l_v = mkLit(v, e.betterPolarity());
    buf_LABests.insert(l_v, e);
}

void LookaheadSMTSolver::updateLAUB(Lit l, int props)
{
    UBVal& val = LAupperbounds[var(l)];
    if (sign(l))
        val.updateUB_n(UBel(props, latest_round));
    else
        val.updateUB_p(UBel(props, latest_round));
}

void LookaheadSMTSolver::setLAExact(Var v, int pprops, int nprops)
{
    LAexacts[v] = ExVal(pprops, nprops, latest_round);
//    if (LABestLit != lit_Undef)
//        LABestLit = LAexacts[var(LABestLit)] < LAexacts[v] ? mkLit(v, nprops > pprops) : LABestLit;
//    else LABestLit = mkLit(v, nprops > pprops);
}

bool LookaheadSMTSolver::createSplit_lookahead()
{
    // Due to the stupidness of the minisat version this gets
    // complicated
    // XXX Now that the version is updated check that this code works!
    int curr_dl0_idx = trail_lim.size() > 0 ? trail_lim[0] : trail.size();
    splits.push_c(SplitData(ca, clauses, trail, curr_dl0_idx, theory_handler, config.smt_split_format_length() == spformat_brief));
    SplitData& sp = splits.last();

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
            sp.addConstraint(tmp);
        }
        p = l;
    }
    printf("\n");

    sp.updateInstance();
    assert(ok);
    return true;
}

