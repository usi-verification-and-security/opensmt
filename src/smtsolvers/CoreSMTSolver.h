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

#include "THandler.h"

#include <cstdio>
#include <iosfwd>
#include <memory>
#include <sstream>

#include <vector>

#include "Vec.h"
#include "Heap.h"
#include "Alg.h"

#include "SolverTypes.h"

#include "Timer.h"

class Proof;
class ModelBuilder;

// Helper method to print Literal to a stream
std::ostream& operator <<(std::ostream& out, Lit l); // MB: Feel free to find a better place for this method.


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
    enum class ConsistencyAction { BacktrackToZero, ReturnUndef, SkipToSearchBegin, NoOp };
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
    bool addOriginalClause_(const vec<Lit> & _ps, opensmt::pair<CRef, CRef> & inOutCRefs);  // Add a clause to the solver without making superflous internal copy. Will change the passed vector 'ps'.  Write the new clause to cr
public:
    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    void    declareVarsToTheories();                 // Declare the seen variables to the theories
    bool    solve        ( const vec< Lit > & assumps );                 // Search for a model that respects a given set of assumptions.
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

    void fillBooleanVars(ModelBuilder & modelBuilder);

    Proof const & getProof() const { assert(proof); return *proof; }

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
    inline void restoreOK          ( )       { ok = true; conflict_frame = 0; }
    inline bool isOK               ( ) const { return ok; } // FALSE means solver is in a conflicting state
    inline int  getConflictFrame   ( ) const { assert(not isOK()); return conflict_frame; }

    template<class C>
    void     printSMTClause   (std::ostream &, const C& );
    void     printSMTClause   (std::ostream &, vec< Lit > &, bool = false );
    void     printSMTClause   (std::ostream &, std::vector<Lit> &, bool = false );

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


protected:
    int processed_in_frozen; // The index in Theory's frozen vec until which frozennes has been processed
    // Helper structures:
    //
    static inline VarData mkVarData(CRef cr, int l)
    {
        VarData d = {cr, l};
        return d;
    }

    void virtual setAssumptions(vec<Lit> const& assumps);

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
    int                 conflict_frame;   // Contains the frame (the assumption literal index+1) where conflict was detected.  (Default is 0)
    uint32_t            n_clauses;        // number of clauses in the problem
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    vec<CRef>           tmp_reas;         // Reasons for minimize_conflicts 2
    int props = 0;
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
    bool*               next_arr;
    std::set<Var>            next_init;
    int                 close_to_prop = 0;
protected:
#ifdef PEDANTIC_DEBUG
public:
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
protected:
#else
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
#endif
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.

    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Map<Var,int, VarHash> assumptions_order; // Defined for active assumption variables: how manyeth active assumption variable this is in assumptions
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              random_seed;      // Used by the random variable selection.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    bool                before_lookahead = true;

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
    int                 unadvised_splits; // How many times the split happened on a PTRef that the logic considers ill-advised
    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    virtual lbool solve_      ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Var doRandomDecision();
    Lit choosePolarity(Var next);
    virtual Var doActivityDecision();
    virtual bool branchLitRandom() { return drand(random_seed) < random_var_freq && !order_heap.empty(); }
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
    virtual bool okContinue   () const;                                                // Check search termination conditions
    virtual ConsistencyAction notifyConsistency() { return ConsistencyAction::NoOp; }  // Called when the search has reached a consistent point
    virtual void notifyEnd() { }                                                       // Called at the end of the search loop
    void     learntSizeAdjust ();                                                      // Adjust learnts size and print something
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();
    virtual lbool zeroLevelConflictHandler();                                          // Common handling of zero-level conflict as it can happen at multiple places

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

    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;


    void     printSMTLit              (std::ostream &, const Lit);

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

    void     printLit         (Lit l) const;
    template<class C>
    void     printClause      (const C& c);
    void     printClause      ( CRef );
    void     printClause      ( Clause& );
    //void     printClause      ( vec< Lit > & );

	void   populateClauses  (vec<PTRef> & clauses, const vec<CRef> & crefs, unsigned int limit = std::numeric_limits<unsigned int>::max());
	void   populateClauses  (vec<PTRef> & clauses, const vec<Lit> & lits);
	std::string printCnfClauses  ();
	std::string printCnfLearnts  ();

    void   printProofSMT2          (std::ostream &); // Print proof
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
    std::vector<unsigned> luby_previous;           // Previously computed luby numbers
    bool               cuvti;                      // For cancelUntilVarTemp
    vec<Lit>           lit_to_restore;             // For cancelUntilVarTemp
    vec<lbool>         val_to_restore;             // For cancelUntilVarTemp
    bool tested = true;
    //
    // Proof production
    //
    bool logsProofForInterpolation() const { return static_cast<bool>(proof); }
    void finalizeProof(CRef finalConflict);
    std::unique_ptr<Proof> proof;                 // (Pointer to) Proof store
    vec< CRef >         pleaves;                  // Store clauses that are still involved in the proof
    // End of proof production
    
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
    // Added Code
    //=================================================================================================
public:

    void    printTrace() const;

protected:

    using SplitClauses = std::vector<vec<Lit>>;
    TPropRes handleNewSplitClauses(SplitClauses & clauses);
};

//=================================================================================================
// Implementation of inline methods:
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
    // FIXME Relocation not compatible at the moment with proof tracking
    if (this->logsProofForInterpolation()) { return; }
    if (ca.wasted() > ca.size() * gf) {
        garbageCollect();
    }
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
inline lbool    CoreSMTSolver::safeValue     (Lit p) const                { auto varValue = safeValue(var(p)); return varValue != l_Undef ? (varValue ^ sign(p)) : l_Undef; }
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
    setAssumptions(assumps);
    return solve_() == l_True;
}

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

inline void CoreSMTSolver::printLit(Lit l) const
{
    std::flush(std::cout);
    std::cerr << l;
    std::flush(std::cerr);
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
    PTRef tr = logic.mkOr(std::move(args));
    auto clause = logic.printTerm(tr);
    fprintf(stderr, "; %s", clause.c_str());
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
		clauses.push(logic.mkOr(std::move(literals)));
	}
}

inline std::string CoreSMTSolver::printCnfClauses()
{
	vec<PTRef> cnf_clauses;
	this->populateClauses(cnf_clauses, clauses);
	
	Logic& logic = theory_handler.getLogic();
	return logic.printTerm(logic.mkAnd(std::move(cnf_clauses)));
}

inline std::string CoreSMTSolver::printCnfLearnts()
{
	vec<PTRef> cnf_clauses;
	this->populateClauses(cnf_clauses, learnts, 2);
	//this->populateClauses(cnf_clauses, trail);
	
	Logic& logic = theory_handler.getLogic();
	return logic.printTerm(logic.mkAnd(std::move(cnf_clauses)));
}


//=================================================================================================
// Added code

template<class C>
inline void CoreSMTSolver::printSMTClause(std::ostream & os, const C& c )
{
    if ( c.size( ) == 0 ) os << "-";
    if ( c.size( ) > 1 ) os << "(or ";
    for (unsigned i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        os << (sign(c[i]) ? "(not " : "") << theory_handler.getVarName(v) << (sign(c[i]) ? ") " : " ");
    }
    if ( c.size( ) > 1 ) os << ")";
}

inline void CoreSMTSolver::printSMTClause(std::ostream & os, vec< Lit > & c, bool ids )
{
    if ( c.size( ) == 0 ) os << "-";
    if ( c.size( ) > 1 ) os << "(or ";
    for (int i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        if ( ids )
            os << (sign(c[i]) ? "-":" ") << v << " ";
        else
        {
            os << (sign(c[i]) ? "(not ":"") << theory_handler.getVarName(v) << (sign(c[i]) ? ") " : " ");
        }
    }
    if ( c.size( ) > 1 ) os << ")";
}

inline void CoreSMTSolver::printSMTClause(std::ostream & os, std::vector< Lit > & c, bool ids )
{
    if ( c.size( ) == 0 ) os << "-";
    if ( c.size( ) > 1 ) os << "(or ";
    for (size_t i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        if ( ids )
            os << (sign(c[i]) ? "-":" ") << v << " ";
        else
        {
            os << (sign(c[i]) ? "(not ":"") << theory_handler.getVarName(v) << (sign(c[i])?") " : " ");
        }
    }
    if ( c.size( ) > 1 ) os << ")";
}

inline void CoreSMTSolver::printSMTLit(std::ostream & os, const Lit l )
{
    Var v = var( l );
    if ( v == 0 ) os << "true";
    else if ( v == 1 ) os << "false";
    else
    {
        os << (sign(l) ? "(not " : "") << theory_handler.getVarName(v) << (sign(l) ? ") " : " ");
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
