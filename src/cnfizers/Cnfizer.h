/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef CNFIZER_H
#define CNFIZER_H

#include "Global.h"
//#include "Otl.h"
#include "SMTSolver.h"
//#include "Egraph.h"
#include "PtStore.h"
#include "SStore.h"

//
// Generic class for conversion into CNF
//
class Cnfizer
{
public:

  Cnfizer( PtStore &   ptstore_
         , SMTSolver & solver_
         , SMTConfig & config_
         , TStore&     symstore_
         , SStore &    sstore_
         , TRef sym_and
         , TRef sym_or
         , TRef sym_not
         , TRef sym_eq
         , SRef sort_bool
         ) :
     ptstore  (ptstore_ )
   , solver   (solver_  )
   , config   (config_  )
   , symstore (symstore_)
   , sstore   (sstore_  )
   , sym_AND  (sym_and  )
   , sym_OR   (sym_or   )
   , sym_NOT  (sym_not  )
   , sym_EQ   (sym_eq   )
   , sort_BOOL(sort_bool)
  { }

  virtual ~Cnfizer( ) { }

  lbool cnfizeAndGiveToSolver ( PTRef
#ifdef PRODUCE_PROOF
                              , const ipartitions_t = 0
#endif
			      ); // Main routine

protected:
  
  virtual bool cnfize	       ( PTRef
#ifdef PRODUCE_PROOF
			       , const ipartitions_t = 0 
#endif
			       ) = 0; // Actual cnfization. To be implemented in derived classes

  bool     deMorganize                ( PTRef
#ifdef PRODUCE_PROOF
                                      , const ipartitions_t &
#endif
                                      ); 	 	                      // Apply deMorgan rules whenever feasible
//  Enode *  rewriteMaxArity            ( Enode *, map< enodeid_t, int > & );   // Rewrite terms using maximum arity

  bool     checkCnf                   ( PTRef );			      // Check if formula is in CNF
  bool     checkDeMorgan              ( PTRef );                            // Check if formula can be deMorganized
  bool     giveToSolver               ( PTRef
#ifdef PRODUCE_PROOF
                                      , const ipartitions_t &
#endif
                                      );                              // Gives formula to the SAT solver

  void  retrieveTopLevelFormulae   ( PTRef, vec<PTRef> & );         // Retrieves the list of top-level formulae
//  void  retrieveClause             ( PTRef, vec<PTRef> & );         // Retrieve a clause from a formula
//  void  retrieveConjuncts          ( PTRef, vec<PTRef> & );         // Retrieve the list of conjuncts

//  Enode * toggleLit		   ( Enode * );                              // Handy function for toggling literals

  PtStore&     ptstore;                                                       // Reference to the term store
  SMTSolver &  solver;                                                        // Reference to Solver
  SMTConfig &  config;                                                        // Reference to Config
  TStore&      symstore;
  SStore &     sstore;

private:

//  void    computeIncomingEdges ( Enode *, map< enodeid_t, int > & );         // Computes the list of incoming edges for a node
//  Enode * mergeEnodeArgs       ( Enode *
//                               , map< enodeid_t, Enode * > &
//                               , map< enodeid_t, int > & );                  // Subroutine for rewriteMaxArity

  bool    checkConj            (PTRef, Map<PTRef,bool,TRefHash,Equal<PTRef> >& check_cache); // Check if a formula is a conjunction
  bool    checkClause          (PTRef, Map<PTRef,bool,TRefHash,Equal<PTRef> >& check_cache); // Check if a formula is a clause
  bool    checkPureConj        (PTRef, Map<PTRef,bool,TRefHash,Equal<PTRef> >& check_cache); // Check if a formula is purely a conjuntion

  // The special boolean symbols
protected:
  TRef  sym_AND;
  TRef  sym_OR;
  TRef  sym_NOT;
  TRef  sym_EQ;
  TRef  sym_XOR;
  SRef  sort_BOOL;

  bool  isLit(PTRef r);
  bool  isBooleanOperator(TRef tr) { return (tr == sym_AND) | (tr == sym_OR) | (tr == sym_NOT) | (tr == sym_EQ) | (tr == sym_XOR); }
  bool  isAtom(PTRef r);
};

#endif
