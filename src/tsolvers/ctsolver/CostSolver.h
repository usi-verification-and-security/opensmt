/*********************************************************************
Author: Anders Franzen <pbct@residual.se>

OpenSMT-CT -- Copyright (C) 2010, Anders Franzen

OpenSMT-CT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT-CT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef COSTSOLVER_H
#define COSTSOLVER_H

#include "TSolver.h"
#include "FastRationals.h"

#include <stack>
#include <list>
#include <vector>
#include <ext/hash_map>
#include <ostream>

/*
 * Solver for the theory of costs
 *
 *   (incur v c t)
 *
 *     v : cost variable
 *     c : A positive number
 *     t : A term
 *
 *     The term t is used to make it possible to ncur the same cost
 *     twice on the same cost variable, e.g. (incur v 1 1), (incur v 1 2)
 *     wil both together incur 2 on v.
 *
 *   (bound v c)
 *
 *     v : cost variable
 *     c : a positive number
 */
class CostSolver : public OrdinaryTSolver
{
  // The type of costs
  typedef Real codomain;

  struct costfun;

  /*
   * Holds a (incur v c t) predicate in a linked list
   * The list maintained sorted on c.
   */
  struct incurnode {
    costfun & fun;
    Enode * atom;
    incurnode * prev;
    incurnode * next;
    codomain cost;
    incurnode( costfun & f, Enode * a, const codomain & c )
      : fun( f ), atom( a ), prev( 0 ), next( 0 ), cost( c ) { }
  };

  /*
   * The header for the linked list
   */
  struct incurlist {
    incurnode * head;
    incurnode * last;
    incurlist() : head( 0 ), last( 0 ) {}
  };

  /*
   * Holds all information for a cost variable:
   *   - All unassigned incur predicates in a sorted linked list
   *   - All assigned incur predicates
   *   - The currently incurred cost
   *   - The sum of the unassigned incurrable costs (slack)
   *   - The current upper and lower bounds
   */
  typedef Enode * bound;
  struct costfun {
    Enode * variable;
    typedef std::vector< incurnode * > nodes_t;
    nodes_t assigned;
    incurlist unassigned;
    codomain incurred;
    codomain slack;
    typedef std::stack< bound > bounds_t;
    bounds_t upperbound;
    bounds_t lowerbound;
    costfun( Enode * var ) : variable( var ), incurred( 0 ), slack( 0 ) { }
  };

  // Hash function for Enode pointers
  struct nodehash {
    size_t operator()( Enode* x ) const
    {
      return __gnu_cxx::hash< size_t >()( reinterpret_cast< size_t >( x ) );
    }
  };

  typedef __gnu_cxx::hash_map< size_t, costfun * > nodemap_ts;
  typedef __gnu_cxx::hash_map< Enode *, costfun *, nodehash > nodemap_t;
  nodemap_t nodemap_;
  typedef __gnu_cxx::hash_map< Enode *, incurnode *, nodehash > incurmap_t;
  incurmap_t incurmap_;

  typedef std::list< costfun * > costfuns_t;
  costfuns_t costfuns_;

  // The atoms causing the current conflict (if any)
  Enode * conflict_;

  // Inform of new atoms
  void add_incur( costfun & fun, Enode * atom, Enode * cost );
  void add_bound( costfun & fun, Enode * atom );

  // Get bound of atom
  const codomain & get_bound( Enode * lbound );
  const codomain & get_incurred( Enode * incur );

  /*
   * Stack of undo operations for backtracking
   */
  enum undo_opcode { REMOVE_LBOUND, REMOVE_UBOUND,
                     REMOVE_INCUR_POS, REMOVE_INCUR_NEG };
  struct undo_op {
    undo_opcode opcode;
    union {
      costfun * fun;
      incurnode * node;
    };
    undo_op( const undo_opcode oc, costfun * f )
      : opcode( oc ), fun( f ) { }
    undo_op( const undo_opcode oc, incurnode * n )
      : opcode( oc ), node( n ) { }
  };
  typedef std::stack< undo_op > undo_ops_t;
  undo_ops_t undo_ops_;
  typedef std::stack< size_t > backtrack_points_t;
  backtrack_points_t backtrack_points_;

  // Debugging output
  void print_status( std::ostream & os );
  void print_status( std::ostream & os, costfun & fun );

  void check_status();

  // Implementation of assertionn of literal
  bool assertLitImpl( Enode * );
public:

  CostSolver( const int           
             , const char *        
	     , SMTConfig &         
	     , Egraph &            
	     , SStore &
	     , vector< Enode * > & 
	     , vector< Enode * > & 
             , vector< Enode * > & );

  ~CostSolver ( );

  lbool               inform              ( Enode * );
  bool                assertLit           ( Enode *, bool = false );
  void                pushBacktrackPoint  ( );
  void                popBacktrackPoint   ( );
  bool                check               ( bool );
  bool                belongsToT          ( Enode * );
  void                computeModel        ( );
};

#endif
