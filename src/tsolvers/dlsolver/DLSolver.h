/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
      , Edgar Pek <edgar.pek@lu.unisi.ch>

OpenSMT2 -- Copyright (C) 2008-2012, Roberto Bruttomesso

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
