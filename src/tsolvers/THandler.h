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

#ifndef THANDLER_H
#define THANDLER_H

#include "TermMapper.h"
#include "TSolverHandler.h"
#include "Theory.h"

class ModelBuilder;

class THandler
{
private:
    Theory &          theory;
    TermMapper &      tmap;                     // Mappings between TRefs and Lits
    vec<bool>         declared;                 // Cache for quick check if given SAT variable has been declared to theory solvers

public:
    using ItpColorMap = std::map<PTRef, icolor_t>;

    THandler(Theory & tsh, TermMapper & termMapper)
    : theory             (tsh)
    , tmap               (termMapper)
    , checked_trail_size (0)
    { }

    ~THandler() = default;

    void clear();  // Clear the solvers from their states

    bool isDeclared (Var v) { return v < declared.size() and declared[v]; } // Has v been declared to the theory solvers?

    Theory& getTheory();// { return theory; }
    Logic&  getLogic() ;// { return theory.getLogic(); }
    const Logic& getLogic() const { return theory.getLogic(); }

    TSolverHandler&       getSolverHandler() ;//      { return theory.getTSolverHandler(); }
    const TSolverHandler& getSolverHandler() const;// { return theory.getTSolverHandler(); }
    TermMapper&           getTMap()      ;//          { return tmap; }

    void    getConflict          ( vec<Lit>&, vec<VarData>&, int & ); // Returns theory conflict in terms of literals
    std::vector<vec<Lit>> getNewSplits(); // Return the new splits as a vector of literals that needs to be interpreted as a clause.

    PTRef   getInterpolant       (const ipartitions_t&, ItpColorMap *, PartitionManager &pmanager);
    Lit     getDeduction         ();                      // Returns a literal that is implied by the current state and the reason literal
    Lit     getSuggestion        ( );                     // Returns a literal that is suggested by the current state
    void    getReason            ( Lit, vec< Lit > &);    // Returns the explanation for a deduced literal

    void fillTheoryFunctions  (ModelBuilder & modelBuilder) const;
    PTRef   varToTerm          ( Var v ) const;//{ return tmap.varToPTRef(v); }  // Return the term ref corresponding to a variable
    Pterm&  varToPterm         ( Var v) ;// { return getLogic().getPterm(tmap.varToPTRef(v)); } // Return the term corresponding to a variable
    Lit     PTRefToLit         ( PTRef tr);// { return tmap.getLit(tr); }

    std::string getVarName     (Var v) const;

    void    pushDeduction      ();// { getSolverHandler().deductions.push({SolverId_Undef, l_Undef}); }  // Add the deduction entry for a variable
    Var     ptrefToVar         ( PTRef r );// { return tmap.getVar(r); }

    void    computeModel      () ;//{ getSolverHandler().computeModel(); } // Computes a model in the solver if necessary
    void    clearModel        ();// { /*getSolverHandler().clearModel();*/ }   // Clear the model if necessary
    bool    assertLits        (const vec<Lit> &);             // Give to the TSolvers the newly added literals on the trail
    bool    assertLit         (PtAsgn pta);// { return getSolverHandler().assertLit(pta); } // Push the assignment to all theory solvers
    void    declareAtom       (PTRef tr);
    void    informNewSplit    (PTRef tr); // Splitting variable data structure updates (e.g., recompute bounds list)
    TRes    check             (bool);       // Check trail in the theories
    void    backtrack         (int);        // Remove literals that are not anymore on the trail

protected:


    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed);
    /*{
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647;
    }*/

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size);
    /*{
        return (int)(drand(seed) * size);
    }*/

    void dumpHeaderToFile(std::ostream&);
    void dumpFormulaToFile(std::ostream&, PTRef, bool negate = false);

#ifdef PEDANTIC_DEBUG
    bool  isOnTrail     ( Lit, vec<Lit>& );
#endif

public:
    vec< PTRef >        stack;                    // Stacked atoms
protected:
    size_t              checked_trail_size;       // Store last size of the trail checked by the solvers

    inline lbool value (Lit p, vec<lbool>& assigns) const;// { return assigns[var(p)] ^ sign(p); }

// Debug
public:
    char* printAsrtClause(vec<Lit>& r);
    char* printAsrtClause(Clause *c);
    bool checkTrailConsistency(vec<Lit>& trail);
protected:
#ifdef PEDANTIC_DEBUG
    std::string printAssertion(Lit);
#endif
};

#endif
