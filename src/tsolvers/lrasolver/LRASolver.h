/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
       , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#ifndef LRASOLVER_H
#define LRASOLVER_H

#include "LRALogic.h"
#include "TSolver.h"
#include "LAVar.h"
#include "LARow.h"
#include "LAColumn.h"

//
// Class to solve Linear Arithmetic theories
//

class LRASolver: public TSolver
{
private:

  LRALogic& logic;
  LAVarStore* lavarStore;
  // Structure to keep backtracking history elements
  class LAVarHistory
  {
  public:
    PTRef e;
    LAVar * v;
    unsigned bound;
    BoundT bound_type;
    LAVarHistory() : e(PTRef_Undef), v(NULL), bound_type(bound_n), bound(0) {}
  };

  // Possible internal states of the solver
  typedef enum
  {
    INIT, INCREMENT, SAT, UNSAT, ERROR
  } LRASolverStatus;

  typedef vector<LAVar *> VectorLAVar;

  opensmt::Real delta; // The size of one delta.  Set through computeModel()
  unsigned bland_threshold;
public:

  LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d);

  ~LRASolver( );                                      // Destructor ;-)

  lbool inform             ( PTRef );                 // Inform LRA about the existence of this constraint
  void  declareTerm        (PTRef tr) { inform(tr); }
  bool  check              ( bool );                  // Checks the satisfiability of current constraints
  bool  assertLit          ( PtAsgn , bool = false ); // Push the constraint into Solver
  void  pushBacktrackPoint ( );                       // Push a backtrack point
  void  popBacktrackPoint  ( );                       // Backtrack to last saved point
  void  computeModel       ( );                       // Computes the model into enodes
  void getConflict(bool, vec<PtAsgn>& e) { for (int i = 0; i < explanation.size(); i++) { e.push(explanation[i]); } } // Return the conflicting bounds
  PtAsgn_reason getDeduction() { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

  Logic& getLogic() { return logic; }
protected:
  // vector in which witnesses for unsatisfiability are stored
  vector<Real> explanationCoefficients;

  VectorLAVar columns;                 // Maps terms' ID to LAVar pointers
  VectorLAVar rows;                    // Maps terms' ID to LAVar pointers, used to store basic columns
  VectorLAVar ptermToLavar;             // Maps original constraints to solver's terms and bounds

  bool assertBoundOnColumn( LAVar * it, unsigned it_i);

  vector<unsigned> checks_history;

  unsigned nVars() const { return columns.size(); }
private:
  void doGaussianElimination( );                          // Performs Gaussian elimination of all redundant terms in the Tableau
  void update( LAVar *, const Delta & );                  // Updates the bounds after constraint pushing
  void pivotAndUpdate( LAVar *, LAVar *, const Delta &);  // Updates the tableau after constraint pushing
  void getConflictingBounds( LAVar *, vec<PTRef> & );     // Returns the bounds conflicting with the actual model
  void refineBounds( );                                   // Compute the bounds for touched polynomials and deduces new bounds from it
  inline bool getStatus( );                               // Read the status of the solver in lbool
  inline bool setStatus( LRASolverStatus );               // Sets and return status of the solver
  void initSolver( );                                     // Initializes the solver
  void print( ostream & out );                            // Prints terms, current bounds and the tableau
  void addVarToRow( LAVar*, LAVar*, Real*);               //
  bool checkIntegersAndSplit();                           //

#ifdef PRODUCE_PROOF
  Enode *             getInterpolants( logic_t & ); // Fill a vector with interpolants
#endif

  bool first_update_after_backtrack;

  LRASolverStatus status;                  // Internal status of the solver (different from bool)
  VectorLAVar slack_vars;                  // Collect slack variables (useful for removal)
  vector<Real *> numbers_pool;             // Collect numbers (useful for removal)
  vector<LAVarHistory> pushed_constraints; // Keeps history of constraints
  set<LAVar *> touched_rows;               // Keeps the set of modified rows

  vector < LAVar * > removed_by_GaussianElimination;       // Stack of variables removed during Gaussian elimination

  // Two reloaded output operators
  inline friend ostream & operator <<( ostream & out, LRASolver & solver )
  {
    solver.print( out );
    return out;
  }

  inline friend ostream & operator <<( ostream & out, LRASolver * solver )
  {
    solver->print( out );
    return out;
  }

  ValPair getValue(PTRef tr) const; // Computes the model and changes state.
  inline int     verbose                       ( ) const { return config.verbosity(); }
  char* printValue(PTRef tr) { char* tmp = (char*)malloc(1); tmp[0] = '\0'; return tmp; } // Implement later...
  char* printExplanation(PTRef tr) { return printValue(tr); } // Implement later...
};

#endif
