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

//
// This is an empty solver to be used as a template for the 
// development of ordinary theory solvers. 
//

#include "EmptySolver.h"

EmptySolver::EmptySolver( const int           i
                        , const char *        n
	                , SMTConfig &         c
	                , Egraph &            e
			, SStore &            t
	                , vector< Enode * > & x
	                , vector< Enode * > & d
                        , vector< Enode * > & s )
  : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{ 
  // Here Allocate External Solver

}

EmptySolver::~EmptySolver( )
{
  // Here Deallocate External Solver

}

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is 
// called before the actual solving starts.
// 
lbool EmptySolver::inform( Enode * e )  
{ 
  (void)e;
  assert( e );
  assert( belongsToT( e ) );
  return l_Undef;
}

// 
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool EmptySolver::assertLit ( Enode * e, bool reason )
{
  (void)e;
  (void)reason;
  assert( e );
  assert( belongsToT( e ) );
  return true;
}

//
// Saves a backtrack point
// You are supposed to keep track of the
// operations, for instance in a vector
// called "undo_stack_term", as happens
// in EgraphSolver
//
void EmptySolver::pushBacktrackPoint ( )
{
}

//
// Restore a previous state. You can now retrieve
// the size of the stack when you pushed the last
// backtrack point. You have to implement the 
// necessary backtrack operations 
// (see for instance backtrackToStackSize( )
// in EgraphSolver)
// Also make sure you clean the deductions you
// did not communicate
//
void EmptySolver::popBacktrackPoint ( )
{
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool EmptySolver::check( bool complete )    
{ 
  (void)complete;
  // Here check for consistency
  return true;
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool EmptySolver::belongsToT( Enode * e )
{
  (void)e;
  assert( e );
  return true;
}

//
// Copy the model into enode's data
//
void EmptySolver::computeModel( )
{
}

#ifdef PRODUCE_PROOF
Enode * EmptySolver::getInterpolants( )
{
  return NULL;
}
#endif
