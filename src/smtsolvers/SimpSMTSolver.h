/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
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

/************************************************************************************[SimpSMTSolver.h]
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

#ifndef SIMP_SMT_SOLVER_H
#define SIMP_SMT_SOLVER_H

#include "Queue.h"
#include "CoreSMTSolver.h"

class SimpSMTSolver : public CoreSMTSolver
{
 public:
    // Constructor/Destructor:
    //
    SimpSMTSolver (SMTConfig &, THandler&);
    ~SimpSMTSolver( );

    void         initialize           ( );

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true) override;

    bool addOriginalSMTClause(const vec<Lit> & smt_clause);
    bool addOriginalSMTClause(const vec<Lit> & smt_clause, pair<CRef, CRef> & inOutCRefs);
public:

    bool    substitute(Var v, Lit x);  // Replace all occurences of v with x (may cause a contradiction).

    // Variable mode:
    // 
    void    setFrozen (Var v, bool b); // If a variable is frozen it will not be eliminated.
    bool    isEliminated(Var v) const;

    // Solving:
    //
    lbool    solve       (const vec<Lit>& assumps, bool do_simp = true, bool turn_off_simp = false);
    lbool    solveLimited(const vec<Lit>& assumps, bool do_simp = true, bool turn_off_simp = false);
    lbool    solve       (                     bool do_simp = true, bool turn_off_simp = false);
    lbool    solve       (Lit p       ,        bool do_simp = true, bool turn_off_simp = false);
    lbool    solve       (Lit p, Lit q,        bool do_simp = true, bool turn_off_simp = false);
    lbool    solve       (Lit p, Lit q, Lit r, bool do_simp = true, bool turn_off_simp = false);
    bool    eliminate   (bool turn_off_elim = false);  // Perform variable elimination based simplification. 

    // Memory managment:
    //
    virtual void garbageCollect() override;


    // Generate a (possibly simplified) DIMACS file:
    //
#if 0
    void    toDimacs  (const char* file, const vec<Lit>& assumps);
    void    toDimacs  (const char* file);
    void    toDimacs  (const char* file, Lit p);
    void    toDimacs  (const char* file, Lit p, Lit q);
    void    toDimacs  (const char* file, Lit p, Lit q, Lit r);
#endif

    // Mode of operation:
    //
    int     grow;              // Allow a variable elimination step to grow by a number of clauses (default to zero).
    int     clause_lim;        // Variables are not eliminated if it produces a resolvent with a length above this limit.
                               // -1 means no limit.
    int     subsumption_lim;   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    double  simp_garbage_frac; // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').

    bool    use_asymm;         // Shrink clauses by asymmetric branching.
    bool    use_rcheck;        // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    bool    use_elim;          // Perform variable elimination.

    // Statistics:
    //
    int     merges;
    int     asymm_lits;
    int     eliminated_vars;

// protected:
  public:

    // Helper structures:
    //
    struct ElimLt {
        const vec<int>& n_occ;
        explicit ElimLt(const vec<int>& no) : n_occ(no) {}

        // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating
        // 32-bit implementation instead then, but this will have to do for now.
        uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; }
        bool operator()(Var x, Var y) const { return cost(x) < cost(y); }
    };

    struct ClauseDeleted {
        const ClauseAllocator& ca;
        explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; } };

    // Solver state:
    //
    int                 elimorder;
    bool                use_simplification;
    OccLists<Var, vec<CRef>, ClauseDeleted>
                        occurs;
    Heap<ElimLt>        elim_heap;
    int                 bwdsub_assigns;
    vec<uint32_t>       elimclauses;
    vec<char>           touched;
    int                 n_touched;

    vec<int>            n_occ;
    Queue<CRef>         subsumption_queue;
    vec<char>           frozen;
    vec<char>           eliminated;

    // Temporaries:
    //
    CRef                bwdsub_tmpunit;

    // Main internal methods:
    //
    using CoreSMTSolver::solve_;
    lbool         solve_                   (bool do_simp, bool turn_off_simp);
    bool          asymm                    (Var v, CRef cr);
    bool          asymmVar                 (Var v);
    void          updateElimHeap           (Var v);
    void          cleanOcc                 (Var v);
    vec<Clause*>& getOccurs                (Var x);
    void          gatherTouchedClauses     ();
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, int& size);
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Var v);
    void          extendModel              ();

    void          removeClause             (CRef cr);
    bool          strengthenClause         (CRef cr, Lit l);
    void          cleanUpClauses           ();
    bool          implied                  (const vec<Lit>& c);
    void          relocAll                 (ClauseAllocator& to);
};


//=================================================================================================
// Implementation of inline methods:


inline bool SimpSMTSolver::isEliminated (Var v) const { return eliminated[v]; }
inline void SimpSMTSolver::updateElimHeap(Var v) {
    assert(use_simplification);

    if (elim_heap.inHeap(v) || (!frozen[v] && !isEliminated(v) && value(v) == l_Undef))
        elim_heap.update(v); }

inline void  SimpSMTSolver::setFrozen    (Var v, bool b) { if ( !use_simplification ) return; frozen[v] = (char)b; if (b) { updateElimHeap(v); } }
inline lbool SimpSMTSolver::solve        (                     bool do_simp, bool turn_off_simp)  { return solve(vec<Lit>{}, do_simp, turn_off_simp); }
inline lbool SimpSMTSolver::solve        (Lit p       ,        bool do_simp, bool turn_off_simp)  { return solve(vec<Lit>{p}, do_simp, turn_off_simp); }
inline lbool SimpSMTSolver::solve        (Lit p, Lit q,        bool do_simp, bool turn_off_simp)  { return solve(vec<Lit>{p,q}, do_simp, turn_off_simp); }
inline lbool SimpSMTSolver::solve        (Lit p, Lit q, Lit r, bool do_simp, bool turn_off_simp)  { return solve(vec<Lit>{p,q,r}, do_simp, turn_off_simp); }
inline lbool SimpSMTSolver::solve        (const vec<Lit>& assumps, bool do_simp, bool turn_off_simp){ 
    budgetOff(); setAssumptions(assumps); return solve_(do_simp, turn_off_simp); }
inline lbool SimpSMTSolver::solveLimited (const vec<Lit>& assumps, bool do_simp, bool turn_off_simp){
    setAssumptions(assumps); return solve_(do_simp, turn_off_simp); }
//inline bool CoreSMTSolver::smtSolve     () { return solve(); }

//=================================================================================================
#endif
