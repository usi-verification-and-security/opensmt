/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#ifndef BITBLASTER_H
#define BITBLASTER_H

#include "Enode.h"
#include "Egraph.h"
#include "MiniSATP.h"
#include "Otl.h"

class BitBlaster
{
public:

   BitBlaster ( const int
              , SMTConfig &
	      , Egraph &
	      , vector< Enode * > &
	      , vector< Enode * > &
              , vector< Enode * > & );
  ~BitBlaster ( );

  lbool inform             ( Enode * );
  bool  check              ( );
  bool  assertLit          ( Enode *, const bool );

  void pushBacktrackPoint  ( );
  void popBacktrackPoint   ( );

  void computeModel        ( ); 

private:

  bool addClause ( vec< Lit > &, Enode * );

  vector< Enode * > & bbEnode      ( Enode * );
  // Predicates
  vector< Enode * > & bbEq         ( Enode * );
  vector< Enode * > & bbBvsle      ( Enode * );
  vector< Enode * > & bbBvule      ( Enode * );
  // Terms
  vector< Enode * > & bbConcat     ( Enode * );
  vector< Enode * > & bbExtract    ( Enode * );
  vector< Enode * > & bbBvand      ( Enode * );
  vector< Enode * > & bbBvor       ( Enode * );
  vector< Enode * > & bbBvxor      ( Enode * );
  vector< Enode * > & bbBvnot      ( Enode * );
  vector< Enode * > & bbBvadd      ( Enode * );
  vector< Enode * > & bbBvmul      ( Enode * );
  vector< Enode * > & bbBvudiv     ( Enode * );
  vector< Enode * > & bbBvurem     ( Enode * );
  vector< Enode * > & bbSignExtend ( Enode * );
  vector< Enode * > & bbVar        ( Enode * );
  vector< Enode * > & bbConstant   ( Enode * );
  vector< Enode * > & bbDistinct   ( Enode * );
  // Not yet considered
  // vector< Enode * > & bbUf         ( Enode * );
  // vector< Enode * > & bbUp         ( Enode * );


  Var      cnfizeAndGiveToSolver ( Enode *, Enode * );           // Cnfize 
  void     cnfizeAnd             ( Enode *, Lit, Enode * );      // Cnfize conjunctions
  void     cnfizeOr              ( Enode *, Lit, Enode * );      // Cnfize disjunctions
  void     cnfizeIff             ( Enode *, Lit, Enode * );      // Cnfize iffs
  void     cnfizeXor             ( Enode *, Lit, Enode * );      // Cnfize xors
  void     cnfizeIfthenelse      ( Enode *, Lit, Enode * );      // Cnfize if then elses

  void     cleanGarbage          ( );                            // Clean garbage on demand

  Enode *  simplify              ( Enode * );                    // Further simplifications
  Enode *  rewriteMaxArity       ( Enode *
                                 , map< int, int > & );
  void     computeIncomingEdges  ( Enode *
                                 , map< int, int > & );          // Computes the list of incoming edges for a node
  Enode *  mergeEnodeArgs        ( Enode *
                                 , map< int, Enode * > &
                                 , map< int, int > & );          // Rewrite terms using maximum arity

  Lit                             constTrue;                     // Constant literal set to true
  Lit                             constFalse;                    // Constant literal set to false

  vector< vector< Enode * > * >   bb_cache;                      // Global cache for bitblasting
  vector< Lit >                   cnf_cache;                     // Global cache for cnfizer
  vector< Var >                   enode_id_to_var;               // Theory atom to Minisat Var correspondence
  vector< Enode * >               var_to_enode;                  // Minisat Var to Theory Atom correspondence
                                                                 
  Egraph &                        E;                             // Egraph store
  SMTConfig &                     config;                        // Configuration

  vector< Enode * > &             explanation;                   // Reference to explanation
  vector< Enode * > &             deductions;                    // Reference to deductions
  vector< Enode * > &             suggestions;                   // Reference to suggestions
  vector< vector< Enode * > * >   garbage;                       // Collect for removal

  vector< Enode * >               variables;                     // Variables
  map< int, Var >                 cnf_var;                       // BB variable to cnf var

  MiniSATP *                      _solverP;                      // Solver with proof logger
  MiniSATP &                      solverP;                       // Solver with proof logger
};

#endif
