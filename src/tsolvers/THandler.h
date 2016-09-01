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
#include "SMTConfig.h"
#include "Deductions.h"
#include "Egraph.h"
#include "Global.h"
#include "TreeOps.h"
#include "TSolverHandler.h"
#include "Theory.h"

class THandler
{
private:
    Theory             &theory;
    TermMapper         &tmap;                     // Mappings between TRefs and Lits
#ifdef PEDANTIC_DEBUG
public:
#endif
    SMTConfig          &config;                   // Reference to configuration
public:

    THandler ( SMTConfig& c, Theory& tsh)
    : theory             (tsh)
    , tmap               (tsh.getTmap())
    , config             (c)
    , checked_trail_size (0)
    { }

    virtual ~THandler ( ) { }

    Theory& getTheory() { return theory; }
    Logic&  getLogic()  { return theory.getLogic(); }

    TSolverHandler&       getSolverHandler()       { return theory.getTSolverHandler(); }
    const TSolverHandler& getSolverHandler() const { return theory.getTSolverHandler(); }
    TermMapper&           getTMap()                { return tmap; }

#ifdef PEDANTIC_DEBUG
    void    getConflict          ( vec<Lit>&, vec<VarData>&, int &, vec<Lit>& ); // Returns theory conflict in terms of literals
#else
    void    getConflict          ( vec<Lit>&, vec<VarData>&, int & ); // Returns theory conflict in terms of literals
#endif
#ifdef PRODUCE_PROOF
    PTRef getInterpolant         (const ipartitions_t&, map<PTRef, icolor_t>*);
#endif
    Lit     getDeduction         ();                      // Returns a literal that is implied by the current state and the reason literal
    Lit     getSuggestion        ( );                     // Returns a literal that is suggested by the current state
    void    getReason            ( Lit, vec< Lit > &);    // Returns the explanation for a deduced literal

    ValPair getValue          (PTRef tr) const { return getSolverHandler().getValue(tr); };

    bool    isTheoryTerm       ( Var v ) { return getLogic().isTheoryTerm(varToTerm(v)); }
    PTRef   varToTerm          ( Var v ) { return tmap.varToPTRef(v); }  // Return the term ref corresponding to a variable
    Pterm&  varToPterm         ( Var v)  { return getLogic().getPterm(tmap.varToPTRef(v)); } // Return the term corresponding to a variable
    Lit     PTRefToLit         ( PTRef tr) { return tmap.getLit(tr); }

    void    getVarName         ( Var v, char** name ) { *name = getLogic().printTerm(tmap.varToPTRef(v)); }

    void    pushDeduction      () { getSolverHandler().deductions.push({SolverId_Undef, l_Undef}); }  // Add the deduction entry for a variable
    Var     ptrefToVar         ( PTRef r ) { return tmap.getVar(r); }

    void    computeModel      () { getSolverHandler().computeModel(); } // Computes a model in the solver if necessary
    bool    assertLits        (vec<Lit>&);             // Give to the TSolvers the newly added literals on the trail
    bool    assertLit         (PtAsgn pta) { return getSolverHandler().assertLit(pta); } // Push the assignment to all theory solvers
    void    declareTermTree   (PTRef tr) { getSolverHandler().declareTermTree(tr); } // Declare the terms in the formula recursively.
    bool    check             (bool);       // Check trail in the theories
    void    backtrack         (int);        // Remove literals that are not anymore on the trail

//    lbool   evaluate          ( PTRef e ) { return l_Undef; }

    char*   printValue         (PTRef tr) { return getSolverHandler().printValue(tr); } // Debug.  Ask from the solvers what they know about value of tr
    char*   printExplanation   (PTRef tr) { return getSolverHandler().printExplanation(tr); } // Debug.  Ask from the solvers what they know about explanation of tr
    void    declareTerm        (PTRef tr) { getSolverHandler().declareTerm(tr); }

protected:


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

//  void verifyCallWithExternalTool        ( bool, size_t );
//  void verifyExplanationWithExternalTool ( vector< Enode * > & );
//  void verifyDeductionWithExternalTool   ( Enode * = NULL );
//  bool callCertifyingSolver              ( const char * );
#ifdef PRODUCE_PROOF
    void verifyInterpolantWithExternalTool ( PTRef itp, const ipartitions_t & );
#endif
    void dumpHeaderToFile(ostream&);
    void dumpFormulaToFile(ostream&, PTRef, bool negate = false);

#ifdef PEDANTIC_DEBUG
    bool  isOnTrail     ( Lit, vec<Lit>& );
#endif

public:
    vec< PTRef >        stack;                    // Stacked atoms
protected:
    size_t              checked_trail_size;       // Store last size of the trail checked by the solvers

    inline lbool value (Lit p, vec<lbool>& assigns) const { return assigns[var(p)] ^ sign(p); }

// Debug
public:
    const char* printAsrtClause(vec<Lit>& r);
    const char* printAsrtClause(Clause *c);
    bool checkTrailConsistency(vec<Lit>& trail);
protected:
#ifdef PEDANTIC_DEBUG
    std::string printAssertion(Lit);
#endif
};

#endif
