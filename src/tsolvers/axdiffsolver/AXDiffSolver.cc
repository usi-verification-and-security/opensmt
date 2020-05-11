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

#include "AXDiffSolver.h"

AXDiffSolver::AXDiffSolver( const int           id
                          , const char *        n
	                  , SMTConfig &         c
	                  , Egraph &            eg
			  , SStore &            t
	                  , vector< Enode * > & x
	                  , vector< Enode * > & de
                          , vector< Enode * > & s )
  : OrdinaryTSolver        ( id, n, c, eg, t, x, de, s )
  , re_p                   ( new RewriteEngine( id, c, eg, t, x, de ) )
  , re                     ( *re_p )
  , nof_index_eqs          ( 0 )
  , nof_asserted_index_eqs ( 0 )
  , nof_read_terms         ( 0 )
  , nof_asserted_read_terms( 0 )
{ }

void AXDiffSolver::initialize( )
{ }

AXDiffSolver::~AXDiffSolver( )
{
  assert( re_p );
  delete re_p;
  re_p = NULL;
}

lbool AXDiffSolver::inform( Enode * e )  
{ 
  if ( config.verbosity > 2 )
    cerr << "# AXDiffSolver::Informing of constraint " << e << endl;

#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 
       || e->getIPartitions( ) != 0 );
#endif

  if ( isIndexEq( e ) )
  {
#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 )
    {
      re.informIdx( e->get1st( ) );
      re.informIdx( e->get2nd( ) );
    }
#endif
    nof_index_eqs ++;
  }

  if ( hasReadTerms( e ) )
    nof_read_terms ++;

  (void)e;
  assert( e );
  assert( belongsToT( e ) );
  return l_Undef;
}

bool AXDiffSolver::assertLit ( Enode * e, bool reason )
{
  if ( config.verbosity > 2 )
    cerr << "# AXDiffSolver::Asserting literal " 
         << ( e->getPolarity( ) == l_True ? "" : "(not " ) 
	 << e 
         << ( e->getPolarity( ) == l_True ? "" : ")" ) 
	 << endl;

  const bool negated = e->getPolarity( ) == l_False;
  assert( e->isEq( ) );

  undo_stack_oper.push_back( ASSERT_LIT );
  undo_stack_term.push_back( e );

  if ( isIndexEq( e ) )
    nof_asserted_index_eqs ++;

  if ( !negated )
  {
    if ( isIndexEq( e ) )
      re.addIndexEq( e );
    else
    {
      if ( hasReadTerms( e ) )
	nof_asserted_read_terms ++;

      re.addEq( e );
    }
  }
  else if ( isElemEq( e ) )
  {
#ifdef PRODUCE_PROOF
    assert( !re.isABcommon( e ) );
    if ( re.isAlocal( e ) )
      re.addNeq( e );
    else
      re.addNeqB( e );
#else
    re.addNeq( e );
#endif
  }

  re.resetStatus( );

  (void)e;
  (void)reason;
  assert( e );
  assert( belongsToT( e ) );
  return true;
}

void AXDiffSolver::pushBacktrackPoint ( )
{
  // Save solver state if required
  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
  backtrack_points.push_back( undo_stack_term.size( ) );
  // re.pushBacktrackPoint( );
}

void AXDiffSolver::popBacktrackPoint ( )
{
  assert( backtrack_points.size( ) > 0 );
  size_t undo_stack_new_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  backtrackToStackSize( undo_stack_new_size );
  // re.popBacktrackPoint( );
}

void AXDiffSolver::backtrackToStackSize( size_t size )
{
  while ( undo_stack_term.size( ) > size )
  {
    oper_t last_action = undo_stack_oper.back( );
    Enode * e = undo_stack_term.back( );

    if ( last_action == ASSERT_LIT )
    {
      const bool negated = e->getPolarity( ) == l_False;
      assert( e->isEq( ) );

      if ( isIndexEq( e ) )
	nof_asserted_index_eqs --;

      if ( !negated )
      {
	if ( isIndexEq( e ) )
	  re.remIndexEq( e );
	else
	{
	  if ( hasReadTerms( e ) )
	    nof_asserted_read_terms --;

	  re.remEq( e );
	}
      }
      else if ( isElemEq( e ) )
      {
#ifdef PRODUCE_PROOF
	assert( !re.isABcommon( e ) );
	if ( re.isAlocal( e ) )
	  re.remNeq( e );
	else
	  re.remNeqB( e );
#else
	re.remNeq( e );
#endif
      }

      if ( config.verbosity > 2 )
	cerr << "# AXDiffSolver::Deasserted literal " 
	     << ( e->getPolarity( ) == l_True ? "" : "(not " ) 
	     << e 
	     << ( e->getPolarity( ) == l_True ? "" : ")" ) 
	     << endl;

      re.resetStatus( );
    }
    else
    {
      opensmt_error( "Unknown case value" );
    }

    undo_stack_oper.pop_back( );
    undo_stack_term.pop_back( );
  }

  assert( undo_stack_term.size( ) == undo_stack_oper.size( ) );
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool AXDiffSolver::check( bool complete )    
{ 
  (void)complete;
  //
  // Skip check until 
  //
  /*
   * DISABILITATE CHIAMATE INDEX-TOTAL
   *
  */
  if ( nof_asserted_index_eqs < nof_index_eqs )
  {
    return true;
  }

  assert( nof_asserted_index_eqs == nof_index_eqs );

  if ( config.verbosity > 2 )
  {
    cerr << "#" << endl
         << "# AXDiffSolver::Checking " << ( complete ? "complete" : "incomplete" ) << endl
	 << "#" << endl;
  }

  // Don't recompute if status is known
  if ( re.getStatus( ) == l_True ) return true;
  if ( re.getStatus( ) == l_False ) return false;

  // 
  // Exhaustive completion of
  // ground and non-ground
  // rewrite rules
  //
  re.check( nof_asserted_index_eqs == nof_index_eqs );

  assert( re.getStatus( ) == l_True 
       || re.getStatus( ) == l_False );

  if ( config.verbosity > 2 )
  {
    cerr << "#" << endl
         << "# AXDiffSolver::Check ends with " 
	 << (re.getStatus( ) == l_True ? "sat" : "unsat" ) << endl
	 << "#" << endl;
  }

  if ( re.getStatus( ) == l_True ) return true;

  return false;
}

bool AXDiffSolver::belongsToT( Enode * e )
{
  // TODO: for now we don't care about this
  (void)e;
  assert( e );
  return true;
}

//
// Copy the model into enode's data
//
void AXDiffSolver::computeModel( )
{
}

bool AXDiffSolver::isIndexEq( Enode * e )
{
  assert( e->isEq( ) );
  Enode * lhs = e->get1st( );
  return lhs->getRetSort( ) == egraph.getSortIndex( );
}

bool AXDiffSolver::isElemEq( Enode * e )
{
  assert( e->isEq( ) );
  Enode * lhs = e->get1st( );
  return lhs->getRetSort( ) == egraph.getSortElem( );
}

bool AXDiffSolver::hasReadTerms( Enode * e )
{
  assert( e->isEq( ) );
  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  return lhs->getRetSort( ) == egraph.getSortElem( )
      && ( ( lhs->isSelect( ) && lhs->get1st( )->isVar( ) )
	|| ( rhs->isSelect( ) && rhs->get1st( )->isVar( ) ) );
}

#ifdef PRODUCE_PROOF
Enode * AXDiffSolver::getInterpolants( )
{
  assert( config.produce_inter != 0 );
  interpolants = egraph.cons( re.getInterpolant( ) );
  return interpolants;
}
#endif
