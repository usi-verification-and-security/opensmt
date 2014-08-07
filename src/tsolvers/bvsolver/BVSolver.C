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

#include "BVSolver.h"

BVSolver::BVSolver ( const int           i
                   , const char *        n
		   , SMTConfig &         c
		   , Egraph &            e
		   , SStore &            t
		   , vector< Enode * > & x
		   , vector< Enode * > & d
                   , vector< Enode * > & s )
 : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{ 
  B = new BitBlaster( id, c, egraph, explanation, deductions, suggestions );  
}

BVSolver::~BVSolver ( ) 
{ 
  delete B;
}

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is 
// called before the actual solving starts.
// 
lbool BVSolver::inform( Enode * e )  
{ 
  assert( e );
  assert( belongsToT( e ) );
  const lbool res = B->inform( e );
  return res;
}

// 
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool BVSolver::assertLit ( Enode * e, bool reason )
{
  (void)reason;
  assert( e );
  assert( belongsToT( e ) );

  assert( e->hasPolarity( ) );
  assert( e->getPolarity( ) == l_False 
       || e->getPolarity( ) == l_True );

  if ( e->isDeduced( ) 
    && e->getPolarity( ) == e->getDeduced( ) 
    && e->getDedIndex( ) == id ) 
    return true;

  const bool n = e->getPolarity( ) == l_False;
  stack.push_back( e );
  const bool res = B->assertLit( e, n );

  assert( res || !explanation.empty( ) );

  return res;
}

//
// Saves a backtrack point
//
void BVSolver::pushBacktrackPoint ( )
{
  backtrack_points.push_back( stack.size( ) );
  //
  // Push a backtrack point inside the bitblaster
  //
  B->pushBacktrackPoint( );
}

//
// Restore a previous state.
// Also make sure you clean the deductions you
// did not communicate
//
void BVSolver::popBacktrackPoint ( )
{
  assert( backtrack_points.size( ) > 0 );
  size_t stack_new_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  //
  // Restore stack size
  //
  while ( stack.size( ) > stack_new_size ) 
  {
    stack.pop_back( );
  }
  //
  // Restore bitblaster state
  //
  B->popBacktrackPoint( );
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool BVSolver::check( bool complete )    
{ 
  if ( !complete ) return true;
  assert( explanation.empty( ) );

  // Here check for consistency
  const bool res = B->check( );

  assert( res || !explanation.empty( ) );
  return res;
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool BVSolver::belongsToT( Enode * e )
{
  assert( e );
  //
  // Standard BV Predicates
  //
  if ( e->isEq       ( )
      /*
    || e->isBvsle    ( ) 
    || e->isBvule    ( )
      */
    || e->isDistinct ( ) )
    return true;
  //
  // Otherwise does not belong
  //
  return false;
}

void BVSolver::computeModel( )
{
  B->computeModel( );
}
