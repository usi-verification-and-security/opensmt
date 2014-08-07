/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
      , Edgar Pek <edgar.pek@lu.unisi.ch>

OpenSMT -- Copyright (C) 2008-2012, Roberto Bruttomesso

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

#ifndef DLSOLVER_H
#define DLSOLVER_H

#include "TSolver.h"
#include "DLGraph.h"

template<class T> class DLSolver : public OrdinaryTSolver
{
public:

  DLSolver( const int           i
          , const char *        n
          , SMTConfig &         c
          , Egraph &            e
	  , SStore &            t
          , vector< Enode * > & x
          , vector< Enode * > & d
	  , vector< Enode * > & s )
	  : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
  {
    initGraph();
  }

  ~DLSolver ( );

  lbool               inform              ( Enode * );
  bool                assertLit           ( Enode *, bool = false );
  void                pushBacktrackPoint  ( );
  void                popBacktrackPoint   ( );
  bool                check               ( bool );
  bool                belongsToT          ( Enode * );
  void                computeModel        ( );
#ifdef PRODUCE_PROOF
  Enode *             getInterpolants( logic_t & );
#endif

private:

  typedef vector< DLEdge<T> * > DLPath;

  void		      initGraph                         ( );
  void		      backtrackToDynEdgesStackSize      ( size_t );
  void		      backtrackToInactiveEnodesStackSize( size_t );
  void		      backtrackToDeducedEdgesStackSize  ( size_t );
  void		      sendDeductions                    ( );

  DLGraph< T > *      G;                         // The graph
  vector< Enode * >   undo_stack_edges;		 // Keeps track of edges present in a graph
  vector< size_t  >   backtrack_points;		 // Keeps track of backtrack points
};

#endif
