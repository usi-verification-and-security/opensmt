/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef MINISATSMTSOLVER_H
#define MINISATSMTSOLVER_H

#define CACHE_POLARITY     0

#include "SMTSolver.h"
#include "THandler.h"

#include <cstdio>
#include "Vec.h"
#include "Heap.h"
#include "Alg.h"

#include "SolverTypes.h"

#include "Timer.h"

#ifdef PRODUCE_PROOF
class Proof;
class ProofGraph;
class Enode;
#endif



// -----------------------------------------------------------------------------------------
// The splits
//
class SplitData
{
    bool                no_instance;    // Does SplitData store the instance?

    vec<vec<Lit> >      constraints;    // The split constraints
    vec<vec<Lit> >      learnts;        // The learnt clauses

    char* litToString(const Lit);
    template<class C> char* clauseToString(const C&);
    char* clauseToString(const vec<Lit>&);
    int getLitSize(const Lit l) const;
    void toPTRefs(vec<vec<PtAsgn> >& out, vec<vec<Lit> >& in, const THandler &thandler);

public:
    SplitData(bool no_instance = true)
        : no_instance(no_instance)

    { assert(no_instance); }
    SplitData(SplitData&& other)
        : no_instance(other.no_instance)
    { other.constraints.moveTo(constraints); other.learnts.moveTo(learnts); }

    SplitData(const SplitData& other)
        : no_instance(other.no_instance)
    { other.constraints.copyTo(constraints); other.learnts.copyTo(learnts); }

    SplitData& operator= (SplitData&& o)
    {
        o.constraints.moveTo(constraints); o.learnts.moveTo(learnts); return *this;
    }

    template<class C> void addConstraint(const C& c)
    {
        constraints.push();
        vec<Lit>& cstr = constraints.last();
        for (int i = 0; i < c.size(); i++)
            cstr.push(c[i]);
    }
    void addLearnt(Clause& c)
    {
        learnts.push();
        vec<Lit>& learnt = learnts.last();
        for (unsigned i = 0; i < c.size(); i++)
            learnt.push(c[i]);
    }

    char* splitToString();
    inline void  constraintsToPTRefs(vec<vec<PtAsgn>>& out, const THandler& thandler) { toPTRefs(out, constraints, thandler); }
    inline void  learntsToPTRefs(vec<vec<PtAsgn>>& out, const THandler& thandler) { toPTRefs(out, learnts, thandler); }
};

inline int SplitData::getLitSize(const Lit l) const
{
    int sz = 0;
    if (sign(l)) sz++;
    Var v = var(l);
    int n = v+1;
    while (n != 0) { n /= 10; sz++; }
    return sz;
}

inline char* SplitData::litToString(const Lit l)
{
    char* l_str;
    asprintf(&l_str, "%s%d", sign(l) ? "-" : "", var(l)+1);
    return l_str;
}

template<class C>
inline char* SplitData::clauseToString(const C& c)
{
    char* c_str = (char*)malloc(1);
    c_str[0] = 0;
    char* c_old = c_str;
    for (int i = 0; i < c.size(); i++)
    {
        char* l_str = litToString(c[i]);
        c_old = c_str;
        asprintf(&c_str, "%s%s ", c_old, l_str);
        free(l_str);
        free(c_old);
    }
    c_old = c_str;
    asprintf(&c_str, "%s0", c_str);
    free(c_old);
    return c_str;
}

inline char* SplitData::splitToString()
{
    int buf_cap = 1024;
    int sz = 0;
    char* buf = (char*) malloc(1024);

/*
    // Units in dl 0
    for (int i = 0; i < (trail_idx > 0 ? trail_idx : trail.size()); i++)
    {
        int n = getLitSize(trail[i]);
        while (buf_cap < sz + n + 4)   // The size of lit, trailing space, the zero, the newline, and NULL
        {
            buf_cap *= 2;
            buf = (char*) realloc(buf, buf_cap);
        }
        sprintf(&buf[sz], "%s%d 0\n", sign(trail[i]) ? "-" : "", var(trail[i])+1);
        sz += n+3; // points to NULL
    }
*/
    // The constraints
    for (int i = 0; i < constraints.size(); i++)
    {
        vec<Lit>& c = constraints[i];
        for (int j = 0; j < c.size(); j++)
        {
            Lit l = c[j];
            int n = getLitSize(l);
            while (buf_cap < sz + n + 2)   // Lit, space, and NULL
            {
                buf_cap *= 2;
                buf = (char*) realloc(buf, buf_cap);
            }
            sprintf(&buf[sz], "%s%d ", sign(l) ? "-" : "", var(l)+1);
            sz += n+1; // Points to the NULL
        }
        while (buf_cap < sz + 3)   // 0, newline, and NULL
        {
            buf_cap *= 2;
            buf = (char*) realloc(buf, buf_cap);
        }
        sprintf(&buf[sz], "0\n");
        sz += 2;
    }

    for (int i = 0; i < learnts.size(); i++)
    {
        vec<Lit>& c = learnts[i];
        for (int j = 0; j < c.size(); j++)
        {
            Lit l = c[j];
            int n = getLitSize(l);
            while (buf_cap < sz + n + 2)   // The size of lit, space, and NULL
            {
                buf_cap *= 2;
                buf = (char*) realloc(buf, buf_cap);
            }
            sprintf(&buf[sz], "%s%d ", sign(l) ? "-" : "", var(l)+1);
            sz += n+1; // points to the null
        }
        while (buf_cap < sz + 3)   // The zero, newline, and the NULL
        {
            buf_cap *= 2;
            buf = (char*) realloc(buf, buf_cap);
        }
        sprintf(&buf[sz], "0\n");
        sz += 2; // Points to the NULL
    }
    buf = (char*) realloc(buf, sz+1);
    return buf;
}

inline void SplitData::toPTRefs(vec<vec<PtAsgn> >& out, vec<vec<Lit> >& in, const THandler& theory_handler)
{
    for (int i = 0; i < in.size(); i++)
    {
        vec<Lit>& c = in[i];
        out.push();
        vec<PtAsgn>& out_clause = out[out.size()-1];
        for (int j = 0; j < c.size(); j++)
        {
            PTRef tr = theory_handler.varToTerm(var(c[j]));
            PtAsgn pta(tr, sign(c[j]) ? l_False : l_True);
            out_clause.push(pta);
        }
    }
}

template<class A, class B>
struct Pair { A first; B second; };



//=================================================================================================
// Solver -- the main class:

class CoreSMTSolver
{
    friend class LookaheadScoreClassic;
    friend class LookaheadScoreDeep;
protected:
    SMTConfig & config;         // Stores Config
    THandler  & theory_handler; // Handles theory
    bool      verbosity;
    bool      init;
public:
    bool stop = false;

    // Constructor/Destructor:
    //
    CoreSMTSolver(SMTConfig&, THandler&);
    virtual ~CoreSMTSolver();
    void     initialize       ( );
    void     clearSearch      ();  // Backtrack SAT solver and theories to decision level 0

    // Problem specification:
    //
protected:
    void  addVar_    (Var v); // Ensure that var v exists in the solver
    virtual Var newVar(bool polarity, bool dvar);//    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.
public:
    void    addVar(Var v); // Anounce the existence of a variable to the solver
    bool    addOriginalClause(const vec<Lit> & ps);
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addOriginalClause(Lit p);                                  // Add a unit clause to the solver.
    bool    addOriginalClause(Lit p, Lit q);                           // Add a binary clause to the solver.
    bool    addOriginalClause(Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver.
protected:
    bool addOriginalClause_(const vec<Lit> & _ps);                                          // Add a clause to the solver
    bool addOriginalClause_(const vec<Lit> & _ps, pair<CRef, CRef> & inOutCRefs);           // Add a clause to the solver without making superflous internal copy. Will change the passed vector 'ps'.  Write the new clause to cr
public:
    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    void    declareVarsToTheories();                 // Declare the seen variables to the theories
    bool    solve        ( const vec< Lit > & assumps );                 // Search for a model that respects a given set of assumptions.
    virtual bool  okay   () const;                  // FALSE means solver is in a conflicting state
    void    crashTest    (int, Var, Var);           // Stress test the theory solver

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);

    // Variable mode:
    //
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   safeValue  (Var x) const;       // The current value of a variable.  l_Undef if the variable does not exist.
    lbool   safeValue  (Lit p) const;       // The current value of a literal.  l_Undef if the literal does not exist.

    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory management:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // External support incremental and backtrackable APIs
    // MB: This is used (and needed) by BitBlaster; can be removed if BitBlaster is re-worked
    void        pushBacktrackPoint ( );
    void        popBacktrackPoint  ( );
    void        reset              ( );
    inline void restoreOK          ( )       { ok = true; }
    inline bool isOK               ( ) const { return ok; }

    template<class C>
    void     printSMTClause   ( ostream &, const C& );
    void     printSMTClause   ( ostream &, vec< Lit > &, bool = false );
    void     printSMTClause   ( ostream &, vector< Lit > &, bool = false );

    // Added Code
    //=================================================================================================

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any). (moded to SMTSolver)
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
    // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    double    var_decay;          // Inverse of the variable activity decay factor.                                            (default 1 / 0.95)
    double    clause_decay;       // Inverse of the clause activity decay factor.                                              (1 / 0.999)
    double    random_var_freq;    // The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02)
    bool      luby_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.
    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.1)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
    bool      expensive_ccmin;    // Controls conflict clause minimization.                                                    (default TRUE)
    int       polarity_mode;      // Controls which polarity the decision heuristic chooses. See enum below for allowed modes. (default polarity_false)

    enum { polarity_true = 0, polarity_false = 1, polarity_user = 2, polarity_rnd = 3 };

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts, conflicts_last_update;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;
#ifdef STATISTICS
    opensmt::OSMTTimeVal search_timer;
    opensmt::OSMTTimeVal branchTimer;
#endif
    double learnts_size;
    uint64_t all_learnts;
    uint64_t learnt_theory_conflicts;
    uint64_t top_level_lits;

    // Splits
    vec<SplitData> splits;
    vec<vec<Lit> > split_assumptions;

protected:
    Lit forced_split; // If theory solver tells that we must split the instance, a literal with unknown value is inserted here for the splitting heuristic
    int processed_in_frozen; // The index in Theory's frozen vec until which frozennes has been processed
    // Helper structures:
    //
    static inline VarData mkVarData(CRef cr, int l)
    {
        VarData d = {cr, l};
        return d;
    }

    struct Watcher
    {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
//=================================================================================================
        // Added Code
        Watcher() : cref(CRef_Undef), blocker(lit_Undef) {}
        // Added Code
        //=================================================================================================
        bool operator==(const Watcher& w) const
        {
            return cref == w.cref;
        }
        bool operator!=(const Watcher& w) const
        {
            return cref != w.cref;
        }
    };

//=================================================================================================
    // Added Code
//    struct watcher_lt
//    {
//        const ClauseAllocator& ca;
//        watcher_lt(const ClauseAllocator& ca_) : ca(ca_) {}
//        bool operator () (const Watcher& x, const Watcher& y)
//        {
//            return ca[x.cref].size() < ca[y.cref].size();
//        }
//    };
    // Added Code
    //=================================================================================================

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const
        {
            return ca[w.cref].mark() == 1;
        }
    };

    struct VarOrderLt
    {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    friend class VarFilter;
    struct VarFilter
    {
        const CoreSMTSolver& s;
        VarFilter(const CoreSMTSolver& _s) : s(_s) {}
        bool operator()(Var v) const { return s.assigns[v] == l_Undef && s.decision[v]; }
    };


    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    uint32_t n_clauses;             // number of clauses in the problem
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    vec<CRef>           tmp_reas;         // Reasons for minimize_conflicts 2
#ifdef PEDANTIC_DEBUG
    vec<Clause*>        debug_reasons;    // Reasons for the theory deduced clauses
    Map<Var,int,VarHash> debug_reason_map; // Maps the deduced lit to the clause used to deduce it
#endif
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>  watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;          // The current assignments (lbool:s stored as char:s).
    vec<bool>           var_seen;
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
protected:
#ifdef PEDANTIC_DEBUG
public:
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
protected:
#else
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
#endif
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
#ifdef PRODUCE_PROOF
    vec< CRef >         units;
#endif
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              random_seed;      // Used by the random variable selection.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    ClauseAllocator     ca{512*1024};
#ifdef CACHE_POLARITY
    vec<char>           prev_polarity;    // The previous polarity of each variable.
#endif


    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    SpUnit   resource_units;
    double   resource_limit;      // Time limit for the search in resource_units
    double   next_resource_limit; // The limit at which the solver needs to stop

    // splitting state vars
    SpType   split_type;

    bool     split_on;
    bool     split_start;
    int      split_num;
    SpUnit   split_units;

    double   split_inittune;                                                           // Initial tuning in units.
    double   split_midtune;                                                            // mid-tuning in units.
    double   split_next;                                                               // When the next split will happen?

    SpPref   split_preference;

    int      unadvised_splits; // How many times the split happened on a PTRef that the logic considers ill-advised
    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    virtual lbool solve_      ();                                                      // Main solve method (assumptions given in 'assumptions').

    void     updateSplitState();                                                       // Update the state of the splitting machine.
    bool     scatterLevel();                                                           // Are we currently on a scatter level.
    bool     createSplit_scatter(bool last);                                           // Create a split formula and place it to the splits vector.
    bool     excludeAssumptions(vec<Lit>& neg_constrs);                                // Add a clause to the database and propagate
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    virtual Lit  pickBranchLit ();                                                     // Return the next decision variable.
    virtual void newDecisionLevel ();                                                  // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    virtual void cancelUntil  (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int nof_conflicts, int nof_learnts);                    // Search for a given number of conflicts.
    bool     okContinue       ();                                                      // Check search termination conditions
    void     runPeriodics     ();                                                      // Run the periodic functions from searcha
    void     learntSizeAdjust ();                                                      // Adjust learnts size and print something
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.

    // Added Line
//    void     boolVarDecActivity( );                    // Decrease boolean atoms activity
    void     claDecayActivity  ( );                    // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity   ( Clause & c );         // Increase a clause with the current 'bump' value.
    // Increase a clause with the current 'bump' value.


    // Operations on clauses:
    //
    virtual void attachClause     (CRef cr);               // Attach a clause to watcher lists.
    virtual void detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef c);             // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
//=================================================================================================
    // Added Code
    void     setReason( Var x, CRef c );
    // Added Code
    //=================================================================================================
    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;


    void     printSMTLit              ( ostream &, const Lit );

#ifdef PRODUCE_PROOF
    void     printRestrictedSMTClause ( ostream &, vec< Lit > &, const ipartitions_t & );
    Enode *  mkRestrictedSMTClause    ( vec< Lit > &, const ipartitions_t & );
#endif
    virtual void verifyModel      ();
    void         checkLiteralCount();

    //ADDED FOR MINIMIZATION
    void     printClause      ( vec< Lit > & );

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed)
    {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647;
    }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size)
    {
        return (int)(drand(seed) * size);
    }


    //=================================================================================================
    // Added Code

public:

    void     printLit         (Lit l);
    template<class C>
    void     printClause      (const C& c);
    void     printClause      ( CRef );
    void     printClause      ( Clause& );
    //void     printClause      ( vec< Lit > & );

	void   populateClauses  (vec<PTRef> & clauses, const vec<CRef> & crefs, unsigned int limit = std::numeric_limits<unsigned int>::max());
	void   populateClauses  (vec<PTRef> & clauses, const vec<Lit> & lits);
	char * printCnfClauses  ();
	char * printCnfLearnts  ();

    bool    smtSolve         ( );             // Solve
    /*
          lbool  getModel               ( Enode * );
    */

#ifdef PRODUCE_PROOF
    void   printProofSMT2          ( ostream & ); // Print proof
    void   printProofDotty         ( );           // Print proof
    void   printInter              ( ostream & ); // Generate and print interpolants
    void   getInterpolants         (const vec<vec<int> >& partitions, vec<PTRef>& interpolants);
    void   getInterpolants         (const vec<ipartitions_t>& partitions, vec<PTRef>& interpolants);
    void   setColoringSuggestions  (  vec< std::map<PTRef, icolor_t>* > * mp );
    bool   getPathInterpolants(vec<PTRef>& interpolants);
    bool   getPathInterpolants(vec<PTRef>& interpolants, const vec<ipartitions_t>& A_masks);
    void   getSingleInterpolant(vec<PTRef>& interpolants);
    void   getSingleInterpolant(vec<PTRef>& interpolants, const ipartitions_t& A_mask);
    void   getSingleInterpolant(std::vector<PTRef>& interpolants, const ipartitions_t& A_mask) // This is a wrapper for the above, used by hifrog
            { vec<PTRef> itps; getSingleInterpolant(itps, A_mask); for (int i = 0; i < itps.size(); i++) interpolants.push_back(itps[i]); }
    bool   getSimultaneousAbstractionInterpolants(vec<PTRef>& interpolants);
    bool   getGenSimultaneousAbstractionInterpolants(vec<PTRef>& interpolants);
    bool   getStateTransitionInterpolants(vec<PTRef>& interpolants);
    bool   getTreeInterpolants(opensmt::InterpolationTree*, vec<PTRef>& interpolants);
    bool   checkImplication( PTRef f1, PTRef f2);

    void   createProofGraph          ();
    inline ProofGraph* getProofGraph ()
    {
        return proof_graph;
    }
    void   deleteProofGraph          ();
    void   reduceProofGraph          ();
    void   checkPartitions           ();
    inline ipartitions_t & getIPartitions ( CRef c )
    {
        assert( clause_to_partition.find( c ) != clause_to_partition.end( ) );
        return clause_to_partition[ c ];
    }

// NOTE old methods, to check
    void   printProof              ( ostream & );
    void   GetInterpolants         (const vector<vector<int> >& partitions, vector<PTRef>& interpolants);
    void   verifyInterpolantWithExternalTool ( vector< PTRef > & );
    inline TheoryInterpolator*                  getTheoryInterpolator( CRef cr )
    {
        assert( clause_to_itpr.find(cr) != clause_to_itpr.end() );
        return clause_to_itpr[ cr ];
    }
    inline void                  setTheoryInterpolator ( CRef cr, TheoryInterpolator* ptr )
    {
        clause_to_itpr[ cr ] = ptr;
    }


#endif

    void   dumpRndInter           (std::ofstream&); // Dumps a random interpolation problem

protected:

#ifdef STATISTICS
    void   printStatistics        ( ostream & );   // Prints statistics
#endif
    void   printTrail             ( );             // Prints the trail (debugging)
    TPropRes checkTheory          (bool, int&);    // Checks consistency in theory.  The second arg is conflictC
    TPropRes checkTheory          (bool complete) { int tmp; return checkTheory(complete, tmp); }
    TPropRes handleSat            ();              // Theory check resulted in sat
    TPropRes handleUnsat          ();              // Theory check resulted in unsat

    void   deduceTheory           (vec<LitLev>&);  // Perform theory-deductions

    int    analyzeUnsatLemma      ( CRef );        // Conflict analysis for an unsat lemma on demand

    void   cancelUntilVar         ( Var );         // Backtrack until a certain variable
    void   cancelUntilVarTempInit ( Var );         // Backtrack until a certain variable
    void   cancelUntilVarTempDone ( );             // Backtrack until a certain variable
    int    restartNextLimit       ( int );         // Next conflict limit for restart
    void   dumpCNF                ( );             // Dumps CNF to cnf.smt2
    vec<CRef>          cleanup;                    // For cleaning up
//    bool               first_model_found;          // True if we found a first boolean model
    double             skip_step;                  // Steps to skip in calling tsolvers
    long               skipped_calls;              // Calls skipped so far
    long               learnt_t_lemmata;           // T-Lemmata stored during search
    long               perm_learnt_t_lemmata;      // T-Lemmata stored during search

    unsigned           luby_i;                     // Keep track of luby index
    unsigned           luby_k;                     // Keep track of luby k
    vector< unsigned > luby_previous;              // Previously computed luby numbers
    bool               cuvti;                      // For cancelUntilVarTemp
    vec<Lit>           lit_to_restore;             // For cancelUntilVarTemp
    vec<lbool>         val_to_restore;             // For cancelUntilVarTemp

#ifdef PRODUCE_PROOF
    //
    // Proof production
    //
    Proof *             proof_;                   // (Pointer to) Proof store
    Proof &             proof;                    // Proof store
    vec< CRef >         pleaves;                  // Store clauses that are still involved in the proof
    ProofGraph *        proof_graph;              // Proof graph
    vec< CRef >         tleaves;                  // Store theory clauses to be removed

    map< CRef, TheoryInterpolator* >  clause_to_itpr;        // Clause id to interpolant (for theory clauses)
    // TODO: Maybe change to vectors
    vector< pair< CRef, ipartitions_t > > units_to_partition;  // Unit clauses and their partitions
    map< CRef, ipartitions_t >            clause_to_partition; // Clause id to interpolant partition
#endif
    //
    // Data structures for DTC
    //
    set< PTRef >     interface_equalities;       // To check that we do not duplicate eij
    set< PTRef >     atoms_seen;                 // Some interface equalities may already exists in the formula
    
    //
    // Data structures required for incrementality, backtrackability
    //
    class undo_stack_el
    {
    public:
        enum oper_t
        {
            NEWVAR
            , NEWUNIT
            , NEWCLAUSE
            , NEWLEARNT
            , NEWAXIOM
#ifdef PRODUCE_PROOF
            , NEWPROOF
            , NEWINTER
#endif
        };
    private:
        oper_t op;
        union
        {
            CRef c;
            Var v;
        };
    public:
        undo_stack_el(oper_t t, CRef c_) : op(t), c(c_)  {}
        undo_stack_el(oper_t t, Var v_) : op(t), v(v_)  {}
        Var  getVar()    const
        {
            assert(op == NEWVAR);
            return v;
        }
        CRef getClause() const
        {
            assert(op == NEWCLAUSE || op == NEWLEARNT || op == NEWAXIOM);
            return c;
        }
        oper_t getType() const
        {
            return op;
        }
    };
    //
    // Automatic push and pop, for enable undo
    //
    vec<size_t>        undo_stack_size;            // Keep track of stack_oper size
    vec<undo_stack_el> undo_stack;                 // Keep track of operations
    vec<int>           undo_trail_size;            // Keep track of trail size
    //
    // TODO: move more data in STATISTICS
    //
#ifdef STATISTICS
    double             preproc_time;
    double             tsolvers_time;
    unsigned           elim_tvars;
    unsigned           total_tvars;
    unsigned           ie_generated;
#endif

    // very debug XXX
#ifdef PEDANTIC_DEBUG
    int                max_dl_debug;
    int                analyze_cnt;
#endif
#ifdef DEBUG_REASONS
    void addTheoryReasonClause_debug(Lit ded, vec<Lit>& reason);
    void checkTheoryReasonClause_debug(Var v);
    void removeTheoryReasonClause_debug(Var v);
#endif
    // Added Code
    //=================================================================================================
public:

    void    printTrace() const;

protected:
    virtual inline void clausesPublish() {};
    virtual inline void clausesUpdate() {};
};

//=================================================================================================
// Implementation of inline methods:
//=================================================================================================
// Added Code
//FIXME inline void CoreSMTSolver::setReason( Var x, CRef c ) { vardata[x].reason = c; }
// Added Code
//=================================================================================================
inline CRef CoreSMTSolver::reason(Var x) const
{
    return vardata[x].reason;
}
inline int  CoreSMTSolver::level (Var x) const
{
    return vardata[x].level;
}

inline void CoreSMTSolver::printTrace() const
{
    int dl = 0;
    for (int i = 0; i < trail.size(); i++)
    {
        if (i == 0 || (trail_lim.size() > dl-1 && trail_lim[dl-1] == i))
            printf("\ndl %d:\n  ", dl++);

        printf("%s%d ", sign(trail[i]) ? "-" : "", var(trail[i]));
    }
    printf("\n");
}

inline void CoreSMTSolver::insertVarOrder(Var x)
{
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x);
}

inline void CoreSMTSolver::varDecayActivity()
{
    var_inc *= var_decay;
}
inline void CoreSMTSolver::varBumpActivity(Var v)
{
    varBumpActivity(v, var_inc);
}
inline void CoreSMTSolver::varBumpActivity(Var v, double inc)
{
    if ( (activity[v] += inc) > 1e100 )
    {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100;
    }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v);
}

//=================================================================================================
// Added Code

inline void CoreSMTSolver::claDecayActivity() { cla_inc *= clause_decay; }
inline void CoreSMTSolver::claBumpActivity (Clause& c)
{
    if ( (c.activity() += cla_inc) > 1e20 )
    {
        // Rescale:
        for (int i = 0; i < learnts.size(); i++)
            ca[learnts[i]].activity() *= 1e-20;
        cla_inc *= 1e-20;
    }
}

inline void CoreSMTSolver::checkGarbage(void) { return checkGarbage(garbage_frac); }
inline void CoreSMTSolver::checkGarbage(double gf)
{
#ifndef PRODUCE_PROOF
    // FIXME Relocation not compatible at the moment with proof tracking
    if (ca.wasted() > ca.size() * gf)
        garbageCollect();
#endif
}

inline bool     CoreSMTSolver::enqueue         (Lit p, CRef from)
{
    return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true);
}

inline bool     CoreSMTSolver::addOriginalClause(const vec<Lit> & ps)
{
    return addOriginalClause_(ps);
}
inline bool     CoreSMTSolver::addEmptyClause  ()
{
    add_tmp.clear();
    return addOriginalClause_(add_tmp);
}
inline bool     CoreSMTSolver::addOriginalClause(Lit p)
{
    add_tmp.clear();
    add_tmp.push(p);
    return addOriginalClause_(add_tmp);
}
inline bool     CoreSMTSolver::addOriginalClause(Lit p, Lit q)
{
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    return addOriginalClause_(add_tmp);
}
inline bool     CoreSMTSolver::addOriginalClause(Lit p, Lit q, Lit r)
{
    add_tmp.clear();
    add_tmp.push(p);
    add_tmp.push(q);
    add_tmp.push(r);
    return addOriginalClause_(add_tmp);
}



inline bool     CoreSMTSolver::locked          (const Clause& c) const
{
    return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && reason(var(c[0])) != CRef_Fake && ca.lea(reason(var(c[0]))) == &c;
}
#ifndef PEDANTIC_DEBUG
inline void     CoreSMTSolver::newDecisionLevel()
{
    trail_lim.push(trail.size());
}
#else
inline void     CoreSMTSolver::newDecisionLevel()
{
    trail_lim.push(trail.size());
    max_dl_debug = decisionLevel() > max_dl_debug ? decisionLevel() : max_dl_debug;
}
#endif

inline int      CoreSMTSolver::decisionLevel ()      const                { return trail_lim.size(); }
inline uint32_t CoreSMTSolver::abstractLevel (Var x) const                { return 1 << (level(x) & 31); }
inline lbool    CoreSMTSolver::value         (Var x) const                { return assigns[x]; }
inline lbool    CoreSMTSolver::value         (Lit p) const                { return assigns[var(p)] ^ sign(p); }
inline lbool    CoreSMTSolver::safeValue     (Var x) const                { if (x < assigns.size()) return value(x); else return l_Undef; }
inline lbool    CoreSMTSolver::safeValue     (Lit p) const                { return safeValue(var(p)); }
inline lbool    CoreSMTSolver::modelValue    (Lit p) const                { return model[var(p)] != l_Undef ? (model[var(p)] ^ sign(p)) : l_Undef; }
inline int      CoreSMTSolver::nAssigns      ()      const                { return trail.size(); }
inline int      CoreSMTSolver::nClauses      ()      const                { return clauses.size(); }
inline int      CoreSMTSolver::nLearnts      ()      const                { return learnts.size(); }
inline int      CoreSMTSolver::nVars         ()      const                { return vardata.size(); }
inline int      CoreSMTSolver::nFreeVars     ()      const                { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     CoreSMTSolver::setPolarity   (Var v, bool b)              { polarity[v] = b; }
inline void     CoreSMTSolver::setDecisionVar(Var v, bool b)
{
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}
inline void     CoreSMTSolver::setConfBudget(int64_t x)                   { conflict_budget    = conflicts    + x; }
inline void     CoreSMTSolver::setPropBudget(int64_t x)                   { propagation_budget = propagations + x; }
inline void     CoreSMTSolver::interrupt()                                { asynch_interrupt = true; }
inline void     CoreSMTSolver::clearInterrupt()                           { asynch_interrupt = false; }
inline void     CoreSMTSolver::budgetOff()                                { conflict_budget = propagation_budget = -1; }
inline bool     CoreSMTSolver::withinBudget() const
{
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget);
}

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.

inline bool     CoreSMTSolver::solve  (const vec<Lit>& assumps)
{
    budgetOff();
    assumps.copyTo(assumptions);
    return solve_() == l_True;
}

inline bool     CoreSMTSolver::okay   () const { return ok; }

inline void     CoreSMTSolver::toDimacs(const char* file)
{
    vec<Lit> as;
    toDimacs(file, as);
}
inline void     CoreSMTSolver::toDimacs(const char* file, Lit p)
{
    vec<Lit> as;
    as.push(p);
    toDimacs(file, as);
}
inline void     CoreSMTSolver::toDimacs(const char* file, Lit p, Lit q)
{
    vec<Lit> as;
    as.push(p);
    as.push(q);
    toDimacs(file, as);
}
inline void     CoreSMTSolver::toDimacs(const char* file, Lit p, Lit q, Lit r)
{
    vec<Lit> as;
    as.push(p);
    as.push(q);
    as.push(r);
    toDimacs(file, as);
}
//=================================================================================================
// Debug + etc:

#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )

static inline void logLit(FILE* f, Lit l)
{
    fprintf(f, "%sx%d", sign(l) ? "~" : "", var(l)+1);
}

static inline void logLits(FILE* f, const vec<Lit>& ls)
{
    fprintf(f, "[ ");
    if (ls.size() > 0)
    {
        logLit(f, ls[0]);
        for (int i = 1; i < ls.size(); i++)
        {
            fprintf(f, ", ");
            logLit(f, ls[i]);
        }
    }
    fprintf(f, "] ");
}

static inline const char* showBool(bool b) { return b ? "true" : "false"; }


// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(bool expr) { (void)expr; assert(expr); }

inline void CoreSMTSolver::printLit(Lit l)
{
    reportf("%s%-3d", sign(l) ? "-" : "", var(l)+1 );
    //reportf("%s%-3d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}


template<class C>
inline void CoreSMTSolver::printClause(const C& c)
{
    for (unsigned i = 0; i < c.size(); i++)
    {
        printLit(c[i]);
        fprintf(stderr, " ");
    }

    Logic& logic = theory_handler.getLogic();
    vec<PTRef> args;
    for (unsigned i = 0; i < c.size(); i++)
    {
        PTRef tr = sign(c[i]) ? logic.mkNot(theory_handler.varToTerm(var(c[i]))) : theory_handler.varToTerm(var(c[i]));
        args.push(tr);
    }
    PTRef tr = logic.mkOr(args);
    char* clause = logic.printTerm(tr);
    fprintf(stderr, "; %s", clause);
    free(clause);
}

inline void CoreSMTSolver::populateClauses(vec<PTRef> & clauses, const vec<CRef> & crefs, unsigned int limit)
{
	Logic& logic = theory_handler.getLogic();
	for (int i = 0; i < crefs.size(); i++) {
		Clause& clause = ca[crefs[i]];
		if (clause.size() > limit) {
			continue;
		}
		vec<PTRef> literals;
		for (unsigned j = 0; j < clause.size(); j++) {
			Lit& literal = clause[j];
			Var v = var(literal);
			PTRef ptr = theory_handler.varToTerm(v);
			if (sign(literal)) ptr = logic.mkNot(ptr);
			literals.push(ptr);
		}
		clauses.push(logic.mkOr(literals));
	}
}

inline void CoreSMTSolver::populateClauses(vec<PTRef> & clauses, const vec<Lit> &lits) {
	Logic& logic = theory_handler.getLogic();
	for (int i = 0; i < lits.size(); i++) {
		const Lit& literal = lits[i];
		Var v = var(literal);
		PTRef ptr = theory_handler.varToTerm(v);
		if (sign(literal)) ptr = logic.mkNot(ptr);
		vec<PTRef> clause;
		clause.push(ptr);
		clauses.push(logic.mkOr(clause));
	}
}

inline char * CoreSMTSolver::printCnfClauses()
{
	vec<PTRef> cnf_clauses;
	this->populateClauses(cnf_clauses, clauses);
	
	Logic& logic = theory_handler.getLogic();
	return logic.printTerm(logic.mkAnd(cnf_clauses));
}

inline char * CoreSMTSolver::printCnfLearnts()
{
	vec<PTRef> cnf_clauses;
	this->populateClauses(cnf_clauses, learnts, 2);
	//this->populateClauses(cnf_clauses, trail);
	
	Logic& logic = theory_handler.getLogic();
	return logic.printTerm(logic.mkAnd(cnf_clauses));
}


//=================================================================================================
// Added code

template<class C>
inline void CoreSMTSolver::printSMTClause( ostream & os, const C& c )
{
    if ( c.size( ) == 0 ) os << "-";
    if ( c.size( ) > 1 ) os << "(or ";
    for (unsigned i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        char* term_name;
        theory_handler.getVarName(v, &term_name);
        os << (sign(c[i])?"(not ":"") << term_name << (sign(c[i])?") ":" ");
        free(term_name);
    }
    if ( c.size( ) > 1 ) os << ")";
}

inline void CoreSMTSolver::printSMTClause( ostream & os, vec< Lit > & c, bool ids )
{
    if ( c.size( ) == 0 ) os << "-";
    if ( c.size( ) > 1 ) os << "(or ";
    for (int i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        if ( ids )
            os << (sign(c[i])?"-":" ") << v << " ";
        else
        {
            char* term_name;
            theory_handler.getVarName(v, &term_name);
            os << (sign(c[i])?"(not ":"") << term_name << (sign(c[i])?") ":" ");
            free(term_name);
        }
    }
    if ( c.size( ) > 1 ) os << ")";
}

inline void CoreSMTSolver::printSMTClause( ostream & os, vector< Lit > & c, bool ids )
{
    if ( c.size( ) == 0 ) os << "-";
    if ( c.size( ) > 1 ) os << "(or ";
    for (size_t i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        if ( ids )
            os << (sign(c[i])?"-":" ") << v << " ";
        else
        {
            char* term_name;
            theory_handler.getVarName(v, &term_name);
            os << (sign(c[i])?"(not ":"") << term_name << (sign(c[i])?") ":" ");
            free(term_name);
        }
    }
    if ( c.size( ) > 1 ) os << ")";
}

inline void CoreSMTSolver::printSMTLit( ostream & os, const Lit l )
{
    Var v = var( l );
    if ( v == 0 ) os << "true";
    else if ( v == 1 ) os << "false";
    else
    {
        char* term_name;
        theory_handler.getVarName(v, &term_name);
        os << (sign(l)?"(not ":"") << term_name << (sign(l)?") ":" ");
        free(term_name);
    }
}

//ADDED FOR MINIMIZATION
inline void CoreSMTSolver::printClause( vec< Lit > & c )
{
    for (int i = 0; i < c.size(); i++)
    {
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}

#endif
