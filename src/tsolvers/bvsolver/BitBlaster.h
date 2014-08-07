/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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
