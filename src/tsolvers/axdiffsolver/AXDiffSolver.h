/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

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

#ifndef AXDIFFSOLVER_H
#define AXDIFFSOLVER_H

#include "TSolver.h"
#include "RewriteEngine.h"

class AXDiffSolver : public OrdinaryTSolver
{
public:

  AXDiffSolver( const int           
              , const char *        
	      , SMTConfig &         
	      , Egraph &            
	      , SStore &
	      , vector< Enode * > & 
	      , vector< Enode * > & 
              , vector< Enode * > & );

  ~AXDiffSolver ( );

  lbool   inform             ( Enode * );
  bool    assertLit          ( Enode *, bool = false );
  void    pushBacktrackPoint ( );
  void    popBacktrackPoint  ( );
  bool    check              ( bool );
  bool    belongsToT         ( Enode * );
  void    computeModel       ( );
#ifdef PRODUCE_PROOF
  Enode * getInterpolants    ( );
  void    gatherIndexes      ( Enode * );
#endif
  void    initialize         ( );

private:

  void backtrackToStackSize  ( size_t );
  bool isIndexEq             ( Enode * );
  bool isElemEq              ( Enode * );
  bool hasReadTerms          ( Enode * );

  //
  // Defines the set of operations that can be performed and that should be undone
  //
  typedef enum { 
    ASSERT_LIT
  } oper_t;

  RewriteEngine * re_p;
  RewriteEngine & re;

  vector< oper_t >  undo_stack_oper;
  vector< Enode * > undo_stack_term;

#ifdef PRODUCE_PROOF
  set< Enode * > indexes;
#endif

  unsigned      nof_index_eqs;
  unsigned      nof_asserted_index_eqs;
  unsigned      nof_read_terms;
  unsigned      nof_asserted_read_terms;
};

#endif
