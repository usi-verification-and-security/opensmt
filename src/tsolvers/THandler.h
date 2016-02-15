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

class THandler
{
protected:
  SolverId my_id;
public:

  THandler ( SMTConfig &   c
           , TermMapper&   tm
           , vec<DedElem>& d
           )
    : deductions         ( d )
    , config             ( c )
    , tmap               ( tm )
    , checked_trail_size ( 0 )
    , tatoms             ( 0 )
    , batoms             ( 0 )
    , tatoms_given       ( 0 )
    , theoryInitialized  (false)
  {
    for (int i = 0; i < SolverDescr::getSolverList().size(); i++) {
        SolverDescr* sd = SolverDescr::getSolverList()[i];
        SolverId id = (SolverId)(*sd);
        while (id.id >= tsolvers.size()) tsolvers.push(NULL);
    }
  }

  virtual ~THandler ( )
  {
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL) delete tsolvers[i];
  }

  virtual Logic&  getLogic  ( )  = 0;

#ifdef PEDANTIC_DEBUG
  void    getConflict          ( vec<Lit>&, vec<int>&, int &, vec<Lit>& ); // Returns theory conflict in terms of literals
#else
  void    getConflict          ( vec<Lit>&, vec<int>&, int & ); // Returns theory conflict in terms of literals
#endif
#ifdef PRODUCE_PROOF
  PTRef getInterpolants      (const ipartitions_t&);                     // Fill a vector with interpolants
#endif
  Lit     getDeduction         ();                      // Returns a literal that is implied by the current state and the reason literal
  Lit     getSuggestion        ( );                     // Returns a literal that is suggested by the current state
#ifdef PEDANTIC_DEBUG
  bool    getReason            ( Lit, vec< Lit > &, vec<char>& );   // Returns the explanation for a deduced literal
#else
  void    getReason            ( Lit, vec< Lit > &, vec<char>& );   // Returns the explanation for a deduced literal
#endif

  ValPair getValue          (PTRef tr) const;

  bool isTheoryTerm         ( Var v ) { return getLogic().isTheoryTerm(varToTerm(v)); }
  PTRef varToTerm           ( Var v ) { return tmap.varToPTRef(v); }  // Return the term ref corresponding to a variable
  Pterm& varToPterm         ( Var v)  { return getLogic().getPterm(tmap.varToPTRef(v)); } // Return the term corresponding to a variable

  void getVarName           ( Var v, char** name ) { *name = getLogic().printTerm(tmap.varToPTRef(v)); }

    Var ptrefToVar          ( PTRef r ) { return tmap.getVar(r); }

//  Var     enodeToVar           ( Enode * );             // Converts enode into boolean variable. Create a new variable if needed
//  Lit     enodeToLit           ( Enode * );             // Converts enode into boolean literal. Create a new variable if needed
//  Lit     enodeToLit           ( Enode *, Var & );      // Converts enode into boolean literal. Create a new variable if needed
//  Enode * varToEnode           ( Var );                 // Return the enode corresponding to a variable
//  void    clearVar             ( Var );                 // Clear a Var in translation table (used in incremental solving)

  void    computeModel         ();                      // Computes a model in the solver if necessary
  bool    assertLits           (vec<Lit>&);             // Give to the TSolvers the newly added literals on the trail
  bool    assertLit            (PtAsgn);                // Push the assignment to all theory solvers
  void    declareTermTree      (PTRef);                 // Declare the terms in the formula recursively.
  bool    check                (bool, vec<Lit>&);       // Check trail in the theories
//  void    backtrack            (vec<Lit>&);             // Remove literals that are not anymore on the trail
  void    backtrack            (int);                   // Remove literals that are not anymore on the trail

  double  getAtomsRatio        ( ) { return (double)batoms/((double)tatoms + 1.0); }

  void    inform               ( );

  lbool   evaluate             ( PTRef e ) { return l_Undef; }

  vec<DedElem>&       deductions; // Var v is deduced by a theory if deductions[v] != l_Undef

  char*   printValue           (PTRef tr); // Debug.  Ask from the solvers what they know about value of tr
  char*   printExplanation     (PTRef tr); // Debug.  Ask from the solvers what they know about explanation of tr
  void declareTerm(PTRef);

protected:

  vec<int> solverSchedule;

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

//  vector< Var >       enode_id_to_var;          // Conversion EnodeID --> Var
//  vector< Enode * >   var_to_enode;             // Conversion Var --> EnodeID
#ifdef PEDANTIC_DEBUG
public:
#endif
  SMTConfig &         config;                   // Reference to configuration
//  SMTSolver &         solver;                   // Reference to SMT Solver
  TermMapper&         tmap;                     // Mappings between TRefs and Lits
//  vec< int > &        level;                    // Reference to SMT Solver level
//  vec< char > &       assigns;                  // Reference to SMT Solver assigns
//  const Var           var_True;                 // To specify constantly true atoms
//  const Var           var_False;                // To specify constantly false atoms
//  Logic &             logic;                    // For true, false literals etc
public:
  vec< PTRef >        stack;                    // Stacked atoms
protected:
  size_t              checked_trail_size;       // Store last size of the trail checked by the solvers

  int                 tatoms;                   // Tracks theory atoms
  int                 batoms;                   // Tracks boolean atoms

  vec< bool >         tatoms_seen;              // Atoms seen
  unsigned            tatoms_given;             // Next atom to give
  vec< ERef >         tatoms_list;              // List of tatoms to communicate later
  vec< bool >         tatoms_give;              // We might want not to give some atoms

  inline lbool value (Lit p, vec<char>& assigns) const { return toLbool(assigns[var(p)]) ^ sign(p); }
public:
  vec<TSolver*>               tsolvers;         // List of ordinary theory solvers
protected:
  bool                        theoryInitialized; // True if theory solvers are initialized


// Debug
public:
  const char* printAsrtClause(vec<Lit>& r);
  const char* printAsrtClause(Clause *c);
  bool checkTrailConsistency(vec<Lit>& trail);
protected:
#ifdef PEDANTIC_DEBUG
  std::string printExplanation(vec<PtAsgn>&, vec<char>&);
  std::string printAssertion(Lit);
#endif
};

#endif
