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

/*
 * FIXME: MANY LINES ARE DISABLED AS THEY HAVE TO BE
 *        FIXED WRT SMTLIB2
 */

#include "BitBlaster.h"

BitBlaster::BitBlaster ( const int i
		       , SMTConfig & c
		       , Egraph & e
                       , vector< Enode * > & ex
                       , vector< Enode * > & d
                       , vector< Enode * > & s )
  : E           ( e )
  , config      ( c ) 
  , explanation ( ex )
  , deductions  ( d )
  , suggestions ( s )
  , _solverP    ( new MiniSATP( i, ex, d, s, var_to_enode, config.bv_theory_propagation > 0 ) )
  , solverP     ( *_solverP )
{ 
  // Attach true
  constTrue = Lit( solverP.newVar( ) );
  vec< Lit > unit;
  unit.push( constTrue );
  addClause( unit, E.mkTrue( ) );
  // Attach false
  unit.pop( );
  constFalse = Lit( solverP.newVar( ) );
  unit.push( ~constFalse );
  addClause( unit, E.mkFalse( ) );
  E.initDupMap2( );
}

BitBlaster::~BitBlaster ( )
{ 
  E.doneDupMap2( );
  delete _solverP;
  cleanGarbage( );
}

//=============================================================================
// Public Interface Routines

lbool 
BitBlaster::inform ( Enode * e ) 
{ 
  vector< Enode * > & result = bbEnode( e );

  assert( result.size( ) == 1 );
  Enode * bb = result.back( );

  if ( bb->isTrue( ) )
    return l_True;
  if ( bb->isFalse( ) )
    return l_False;

  Var var = cnfizeAndGiveToSolver( bb, e );
  if ( (int)enode_id_to_var.size( ) <= e->getId( ) )
    enode_id_to_var.resize( e->getId( ) + 1, var_Undef );
  assert( enode_id_to_var[ e->getId( ) ] == var_Undef );
  enode_id_to_var[ e->getId( ) ] = var; 
  if ( (int)var_to_enode.size( ) <= var )
    var_to_enode.resize( var + 1, NULL );
  assert( var_to_enode[ var ] == NULL );
  var_to_enode[ var ] = e;

  return l_Undef;
}

bool
BitBlaster::assertLit ( Enode * e, const bool n )
{
  assert( e );
  assert( e->isTAtom( ) );

  assert( static_cast< int >( enode_id_to_var.size( ) ) > e->getId( ) );
  assert( enode_id_to_var[ e->getId( ) ] != var_Undef );
  Var act_var = enode_id_to_var[ e->getId( ) ];

  if ( (n && act_var == var(constTrue) ) 
    ||       act_var == var(constFalse) )
    return false;
  //
  // Activate clause for e
  //
  vec< Lit > clause;
  clause.push( Lit( act_var, n ) );
  bool res = addClause( clause, e ); 

  return res;
}

bool 
BitBlaster::check( )
{ 
  const bool res = solverP.solve( );
  assert( res || !explanation.empty( ) );
  return res;
}

void
BitBlaster::pushBacktrackPoint ( )
{
  solverP.pushBacktrackPoint( );
}

void 
BitBlaster::popBacktrackPoint ( )
{ 
  // Pop solver
  solverP.popBacktrackPoint( );
  solverP.restoreOK( );
}

//=============================================================================
// BitBlasting Routines

vector< Enode * > &
BitBlaster::bbEnode ( Enode * e )
{
  //
  // BitBlasts predicates
  //
  if ( e->isEq         ( ) ) return bbEq         ( e );
  /*
  if ( e->isBvsle      ( ) ) return bbBvsle      ( e );
  if ( e->isBvule      ( ) ) return bbBvule      ( e );
  */
  if ( e->isDistinct   ( ) ) return bbDistinct   ( e );
  // if ( e->isUp         ( ) ) return bbUp         ( e );
  //                   
  // BitBlasts terms  
  //
  /*                   
  if ( e->isConcat     ( ) ) return bbConcat     ( e );
  if ( e->isExtract    ( ) ) return bbExtract    ( e );
  if ( e->isBvand      ( ) ) return bbBvand      ( e );
  if ( e->isBvor       ( ) ) return bbBvor       ( e );
  if ( e->isBvxor      ( ) ) return bbBvxor      ( e );
  if ( e->isBvnot      ( ) ) return bbBvnot      ( e );
  if ( e->isBvadd      ( ) ) return bbBvadd      ( e );
  if ( e->isBvmul      ( ) ) return bbBvmul      ( e );
  if ( e->isBvudiv     ( ) ) return bbBvudiv     ( e );
  if ( e->isBvurem     ( ) ) return bbBvurem     ( e );
  if ( e->isSignExtend ( ) ) return bbSignExtend ( e );
  */
  if ( e->isVar        ( ) ) return bbVar        ( e );
  if ( e->isConstant   ( ) ) return bbConstant   ( e );
  // if ( e->isUf         ( ) ) return bbUf         ( e );
  //
  // Exit if term is not handled
  //
  opensmt_error2( "term not handled (yet ?)", e );
}

//
// Equality
//
vector< Enode * > &
BitBlaster::bbEq( Enode * e )
{ 
  assert( e );
  assert( e->isEq( ) ); 

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collection
  garbage.push_back( result );

  assert( e->getArity( ) == 2 );
  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );

  assert( !lhs->isConstant( ) || !rhs->isConstant( ) );

  // Retrieve arguments' encodings
  vector< Enode * > & bb_lhs = bbEnode( lhs );
  vector< Enode * > & bb_rhs = bbEnode( rhs );

  assert( bb_lhs.size( ) == bb_rhs.size( ) );
  assert( (int)bb_lhs.size( ) == lhs->getWidth( ) );

  // Produce the result
  Enode * result_args = const_cast< Enode * >(E.enil);
  for ( unsigned i = 0 ; i < bb_lhs.size( ) ; i ++ )
  {
    Enode * args = E.cons( bb_lhs[ i ], E.cons( bb_rhs[ i ] ) );
    result_args  = E.cons( E.mkIff( args ), result_args );
  }
  result->push_back( simplify( E.mkAnd( result_args ) ) );
  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Signed less than equal
//
vector< Enode * > &
BitBlaster::bbBvsle( Enode * e )
{ 
  assert( e );
  // assert( e->isBvsle( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  assert( e->getArity( ) == 2 );
  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  assert( lhs->getWidth( ) >= 2 );

  // Retrieve arguments' encodings
  vector< Enode * > & bb_lhs = bbEnode( lhs );
  vector< Enode * > & bb_rhs = bbEnode( rhs );
  assert( bb_lhs.size( ) == bb_rhs.size( ) );
  assert( (int)bb_lhs.size( ) == lhs->getWidth( ) );
  //
  // Produce lhs < rhs
  //
  Enode * lt_prev = NULL;
  for ( unsigned i = 0 ; i < bb_lhs.size( ) - 1 ; i ++ )
  {
    // Produce ~l[i] & r[i]
    Enode * not_l   = E.mkNot( E.cons( bb_lhs[ i ] ) );
    Enode * lt_this = E.mkAnd( E.cons( not_l 
			     , E.cons( bb_rhs[ i ] ) ) );
    // Produce l[i] <-> r[i]
    Enode * eq_this = E.mkIff( E.cons( bb_lhs[ i ] 
	                     , E.cons( bb_rhs[ i ] ) ) );
    if ( lt_prev )
    {
      Enode * or_args = E.cons( lt_this
		      , E.cons( E.mkAnd( E.cons( eq_this
			               , E.cons( lt_prev ) ) ) ) );
      lt_prev = E.mkOr( or_args );
    }
    else
    {
      lt_prev = lt_this;
    }
  }

  assert( lt_prev );
  Enode * not_r   = E.mkNot( E.cons( bb_rhs.back( ) ) );
  Enode * neg_pos = E.mkAnd( E.cons( bb_lhs.back( ), E.cons( not_r ) ) );
  Enode * eq_this = E.mkIff( E.cons( bb_lhs.back( ), E.cons( bb_rhs.back( ) ) ) );
  Enode * lt_part = E.mkOr ( E.cons( E.mkAnd( E.cons( eq_this, E.cons( lt_prev ) ) ), E.cons( neg_pos ) ) );

  vector< Enode * > & eq_part = bbEnode( E.mkEq( E.cons( lhs, E.cons( rhs ) ) ) );
  //
  // Produce (lhs=rhs | lhs<rhs)
  //
  result->push_back( simplify( E.mkOr( E.cons( eq_part.back( ), E.cons( lt_part ) ) ) ) );

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Unsigned less than equal
//
vector< Enode * > &
BitBlaster::bbBvule( Enode * e )
{ 
  assert( e );
  //
  // What ? Isn't it an eq ? Well lt are translated into le
  // in creation, still we want to encode le as if it was
  // an eq, as le = lt or eq
  //
  // Later comment: What did I mean ?? :-)
  //
  // assert( e->isBvule( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  assert( e->getArity( ) == 2 );
  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  // Retrieve arguments' encodings
  vector< Enode * > & bb_lhs = bbEnode( lhs );
  vector< Enode * > & bb_rhs = bbEnode( rhs );
  assert( bb_lhs.size( ) == bb_rhs.size( ) );
  assert( (int)bb_lhs.size( ) == lhs->getWidth( ) );
  //
  // Produce the result
  //
  Enode * lt_prev = NULL;
  for ( unsigned i = 0 ; i < bb_lhs.size( ) ; i ++ )
  {
    // Produce ~l[i] & r[i]
    Enode * not_l   = E.mkNot( E.cons( bb_lhs[ i ] ) );
    Enode * lt_this = E.mkAnd( E.cons( not_l 
			     , E.cons( bb_rhs[ i ] ) ) );
    // Produce l[i] <-> r[i]
    Enode * eq_this = E.mkIff( E.cons( bb_lhs[ i ] 
	                     , E.cons( bb_rhs[ i ] ) ) );
    if ( lt_prev )
    {
      Enode * or_args = E.cons( lt_this
		      , E.cons( E.mkAnd( E.cons( eq_this
			               , E.cons( lt_prev ) ) ) ) );
      lt_prev = E.mkOr( or_args );
    }
    else
    {
      lt_prev = lt_this;
    }
  }
  
  Enode * lt_part = lt_prev;
  vector< Enode * > & eq_part = bbEnode( E.mkEq( E.cons( lhs, E.cons( rhs ) ) ) );
  //
  // Produce (lhs=rhs | lhs<rhs)
  //
  result->push_back( simplify( E.mkOr( E.cons( eq_part.back( ), E.cons( lt_part ) ) ) ) );
  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Concatenation
//
vector< Enode * > &
BitBlaster::bbConcat( Enode * e ) 
{ 
  assert( e );
  // assert( e->isConcat( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  vector< Enode * > stack;
  // Retrieve arguments and put on the stack
  for ( Enode * list = e->getCdr( ) ; !list->isEnil( ) ; list = list->getCdr( ) )
    stack.push_back( list->getCar( ) );

  while( !stack.empty( ) )
  {
    Enode * arg = stack.back( );
    stack.pop_back( );
    // Retrieve bb encoding
    vector< Enode * > & bb_arg = bbEnode( arg );
    // Produce result
    for ( unsigned i = 0 ; i < bb_arg.size( ) ; i ++ )
      result->push_back( bb_arg[ i ] );
  }

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

// 
// Extraction
//
vector< Enode * > &
BitBlaster::bbExtract( Enode * e ) 
{ 
  assert( e );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  int lsb = 0, msb = 0;

  /*
  assert( e->isExtract( ) );
  e->isExtract( &msb, &lsb );
  */
  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  assert( e->getArity( ) == 1 );
  Enode * arg = e->get1st( );
  // Retrieve arguments' encodings
  vector< Enode * > & bb_arg = bbEnode( arg );
  // Produce the result
  for ( int i = lsb ; i <= msb ; i ++ )
    result->push_back( bb_arg[ i ] );

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Bitwise AND
//
vector< Enode * > &
BitBlaster::bbBvand( Enode * e ) 
{
  assert( e );
  // assert( e->isBvand( ) );

  assert( e->get1st( )->getWidth( ) == e->get2nd( )->getWidth( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  vector< vector< Enode * > * > bb_args;

  for ( Enode * list = e->getCdr( ) 
      ; !list->isEnil( ) 
      ; list = list->getCdr( ) )
  {
    Enode * arg = list->getCar( );
    bb_args.push_back( &bbEnode( arg ) );
    assert( bb_args.back( ) );
  }

  for ( unsigned i = 0 ; i < bb_args.back( )->size( ) ; i ++ )
  {
    Enode * bb_list = const_cast< Enode * >( E.enil );
    for ( unsigned j = 0 ; j < bb_args.size( ) ; j ++ )
    {
      assert( (*(bb_args[ j ]))[ i ] );
      bb_list = E.cons( (*(bb_args[ j ]))[ i ], bb_list );
    }
    result->push_back( E.mkAnd( bb_list ) );
  }

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Bitwise OR
//
vector< Enode * > &
BitBlaster::bbBvor( Enode * e ) 
{
  assert( e );
  // assert( e->isBvor( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  vector< vector< Enode * > * > bb_args;

  for ( Enode * list = e->getCdr( ) 
      ; !list->isEnil( ) 
      ; list = list->getCdr( ) )
  {
    Enode * arg = list->getCar( );
    bb_args.push_back( &bbEnode( arg ) );
  }

  for ( unsigned i = 0 ; i < bb_args.back( )->size( ) ; i ++ )
  {
    Enode * bb_list = const_cast< Enode * >( E.enil );
    for ( unsigned j = 0 ; j < bb_args.size( ) ; j ++ )
      bb_list = E.cons( (*(bb_args[ j ]))[ i ], bb_list );
    result->push_back( E.mkOr( bb_list ) );
  }

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Bitwise XOR
//
vector< Enode * > &
BitBlaster::bbBvxor( Enode * e ) 
{ 
  assert( e );
  // assert( e->isBvxor( ) );
  assert( e->getArity( ) == 2 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  vector< Enode * > & bb_lhs = bbEnode( lhs );
  vector< Enode * > & bb_rhs = bbEnode( rhs );

  for ( unsigned i = 0 ; i < bb_lhs.size( ) ; i ++ )
    result->push_back( E.mkXor( E.cons( bb_lhs[ i ], E.cons( bb_rhs[ i ] ) ) ) );

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

//
// Bitwise NOT
//
vector< Enode * > &
BitBlaster::bbBvnot( Enode * e ) 
{ 
  assert( e );
  // assert( e->isBvnot( ) );
  assert( e->getArity( ) == 1 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  Enode * arg = e->get1st( );
  vector< Enode * > & bb_arg = bbEnode( arg );

  for ( unsigned i = 0 ; i < bb_arg.size( ) ; i ++ )
    result->push_back( E.mkNot( E.cons( bb_arg[ i ] ) ) );

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

vector< Enode * > &
BitBlaster::bbBvadd( Enode * e ) 
{ 
  assert( e );
  // assert( e->isBvadd( ) );
  assert( e->getArity( ) == 2 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  Enode * arg1 = e->get1st( );
  Enode * arg2 = e->get2nd( );
  vector< Enode * > & bb_arg1 = bbEnode( arg1 );
  vector< Enode * > & bb_arg2 = bbEnode( arg2 );
  assert( bb_arg1.size( ) == bb_arg2.size( ) );

  Enode * carry = NULL;

  for( unsigned i = 0 ; i < bb_arg1.size( ) ; i++ ) 
  {
    Enode * bit_1 = bb_arg1[ i ];
    Enode * bit_2 = bb_arg2[ i ];
    assert( bit_1 );
    assert( bit_2 );

    Enode * xor_1 = E.mkXor( E.cons( bit_1 , E.cons( bit_2 ) ) );
    Enode * and_1 = E.mkAnd( E.cons( bit_1 , E.cons( bit_2 ) ) );

    if ( carry ) 
    {    
      Enode * xor_2 = E.mkXor( E.cons( xor_1 , E.cons( carry ) ) );
      Enode * and_2 = E.mkAnd( E.cons( xor_1 , E.cons( carry ) ) );
      carry = E.mkOr( E.cons( and_1 , E.cons( and_2 ) ) );
      result->push_back( xor_2 );
    }    
    else 
    {    
      carry = and_1;
      result->push_back( xor_1 );
    }    
  }

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

vector< Enode * > &
BitBlaster::bbBvudiv( Enode * e ) 
{ 
  assert( e );
  // assert( e->isBvudiv( ) );
  assert( e->getArity( ) == 2 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];
  //
  // Allocate new result
  //
  vector< Enode * > * result = new vector< Enode * >;
  //
  // Garbage collect
  //
  garbage.push_back( result );
  vector< Enode * > minuend;
  Enode * arg1 = e->get1st( );
  Enode * arg2 = e->get2nd( );
  vector< Enode * > & dividend = bbEnode( arg1 );
  vector< Enode * > & divisor = bbEnode( arg2 );
  assert( divisor.size( ) == dividend.size( ) );
  //
  // Generate condition divisor != 0
  //
  char buf[ 32 ];
  sprintf( buf, "bv0[%d]", arg2->getWidth( ) );
  Enode * zero = NULL;/*E.mkBvnum( buf );*/
  Enode * div_eq_zero = bbEnode( E.mkEq( E.cons( arg2, E.cons( zero ) ) ) ).back( );

  const unsigned size = divisor.size( );
  (*result).resize( size, NULL );
  //
  // Initialize minuend as 0..0 q[n-1]
  //
  minuend.push_back( dividend[ size - 1 ] );
  for ( unsigned i = 1 ; i < size ; i ++ )
    minuend.push_back( E.mkFalse( ) );
  //
  // Main loop
  //
  for ( int i = size - 1 ; i >= 0 ; i -- )
  {
    //
    // Compute result[ i ] = !(minuend < divisor);
    //
    Enode * lt_prev = NULL;
    for ( unsigned j = 0 ; j < size ; j ++ )
    {
      // Produce ~l[j] & r[j]
      Enode * not_l   = E.mkNot( E.cons( minuend[ j ] ) );
      Enode * lt_this = E.mkAnd( E.cons( not_l 
	                       , E.cons( divisor[ j ] ) ) );
      // Produce l[j] <-> r[j]
      Enode * eq_this = E.mkIff( E.cons( minuend[ j ] 
	                       , E.cons( divisor[ j ] ) ) );
      if ( lt_prev )
      {
	Enode * or_args = E.cons( lt_this
	                , E.cons( E.mkAnd( E.cons( eq_this
		                         , E.cons( lt_prev ) ) ) ) );
	lt_prev = E.mkOr( or_args );
      }
      else
      {
	lt_prev = lt_this;
      }
    }

    assert( lt_prev );

    // Old
    // (*result)[ i ] = E.mkNot( E.cons( lt_prev ) );
    // divisor != 0 -> !lt_prev
    // divisor == 0 || !lt_prev
    (*result)[ i ] = E.mkOr( E.cons( div_eq_zero, E.cons( E.mkNot( E.cons( lt_prev ) ) ) ) );
    Enode * bit_i = (*result)[ i ];
    // 
    // Construct subtrahend
    // 
    vector< Enode * > subtrahend;
    for ( unsigned j = 0 ; j < size ; j ++ )
    {
      subtrahend.push_back( E.mkAnd( E.cons( bit_i
	                           , E.cons( divisor[ j ] ) ) ) );
    }
    //
    // Subtract and store in minuend
    //
    Enode * carry = NULL;
    for( unsigned j = 0 ; j < minuend.size( ) ; j++ ) 
    {
      Enode * bit_1 = minuend[ j ];
      Enode * bit_2 = subtrahend[ j ];
      assert( bit_1 );
      assert( bit_2 );

      Enode * bit_2_neg = E.mkNot( E.cons( bit_2 ) );
      Enode * xor_1 = E.mkXor( E.cons( bit_1, E.cons( bit_2_neg ) ) );
      Enode * and_1 = E.mkAnd( E.cons( bit_1, E.cons( bit_2_neg ) ) );

      if ( carry ) 
      {    
	Enode * xor_2 = E.mkXor( E.cons( xor_1, E.cons( carry ) ) );
	Enode * and_2 = E.mkAnd( E.cons( xor_1, E.cons( carry ) ) );
	carry = E.mkOr( E.cons( and_1, E.cons( and_2 ) ) );
	minuend[ j ] = xor_2;
      }    
      else 
      {    
	carry = and_1;
	minuend[ j ] = xor_1;
      }    
    }
  
    carry = NULL;

    //
    // Adds one, if bit_i is one
    //
    for( unsigned j = 0 ; j < minuend.size( ) ; j++ ) 
    {
      Enode * bit_1 = minuend[ j ];
      Enode * bit_2 = j == 0 ? E.mkTrue( ) : E.mkFalse( );
      assert( bit_1 );
      assert( bit_2 );

      Enode * xor_1 = E.mkXor( E.cons( bit_1, E.cons( bit_2 ) ) );
      Enode * and_1 = E.mkAnd( E.cons( bit_1, E.cons( bit_2 ) ) );

      if ( carry ) 
      {    
	Enode * xor_2 = E.mkXor( E.cons( xor_1, E.cons( carry ) ) );
	Enode * and_2 = E.mkAnd( E.cons( xor_1, E.cons( carry ) ) );
	carry = E.mkOr( E.cons( and_1, E.cons( and_2 ) ) );
	minuend[ j ] = xor_2;
      }    
      else 
      {    
	carry = and_1;
	minuend[ j ] = xor_1;
      }    
    }

    if ( i > 0 )
    {
      //
      // Prepare new minuend
      //
      //                M[i-1]
      //
      // O[2] O[1] O[0]
      //      N[2] N[1] N[0]
      //
      for ( int j = size - 1 ; j >= 1 ; j -- )
	minuend[ j ] = minuend[ j - 1 ];
      minuend[ 0 ] = dividend[ i - 1 ];
    }
  }
  //
  // Save result and return
  //
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

vector< Enode * > &
BitBlaster::bbBvurem( Enode * e ) 
{ 
  assert( e );
  // assert( e->isBvurem( ) );
  assert( e->getArity( ) == 2 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];
  //
  // Allocate new result
  //
  vector< Enode * > * result = new vector< Enode * >;
  //
  // Garbage collect
  //
  garbage.push_back( result );

  vector< Enode * > minuend;
  Enode * arg1 = e->get1st( );
  Enode * arg2 = e->get2nd( );
  vector< Enode * > & dividend = bbEnode( arg1 );
  vector< Enode * > & divisor = bbEnode( arg2 );
  assert( divisor.size( ) == dividend.size( ) );
  //
  // Generate condition divisor != 0
  //
  char buf[ 32 ];
  sprintf( buf, "bv0[%d]", arg2->getWidth( ) );
  Enode * zero = NULL;/*E.mkBvnum( buf );*/
  Enode * div_eq_zero = bbEnode( E.mkEq( E.cons( arg2, E.cons( zero ) ) ) ).back( );

  const unsigned size = divisor.size( );
  (*result).resize( size, NULL );
  //
  // Initialize minuend as 0..0 q[n-1]
  //
  minuend.push_back( dividend[ size - 1 ] );
  for ( unsigned i = 1 ; i < size ; i ++ )
    minuend.push_back( E.mkFalse( ) );
  //
  // Main loop
  //
  for ( int i = size - 1 ; i >= 0 ; i -- )
  {
    //
    // Compute result[ i ] = !(minuend < divisor);
    //
    Enode * lt_prev = NULL;
    for ( unsigned j = 0 ; j < size ; j ++ )
    {
      // Produce ~l[j] & r[j]
      Enode * not_l   = E.mkNot( E.cons( minuend[ j ] ) );
      Enode * lt_this = E.mkAnd( E.cons( not_l 
	                       , E.cons( divisor[ j ] ) ) );
      // Produce l[j] <-> r[j]
      Enode * eq_this = E.mkIff( E.cons( minuend[ j ] 
	                       , E.cons( divisor[ j ] ) ) );
      if ( lt_prev )
      {
	Enode * or_args = E.cons( lt_this
	                , E.cons( E.mkAnd( E.cons( eq_this
		                         , E.cons( lt_prev ) ) ) ) );
	lt_prev = E.mkOr( or_args );
      }
      else
      {
	lt_prev = lt_this;
      }
    }

    assert( lt_prev );
    Enode * bit_i = E.mkNot( E.cons( lt_prev ) );

    // 
    // Construct subtrahend
    // 
    vector< Enode * > subtrahend;
    for ( unsigned j = 0 ; j < size ; j ++ )
      subtrahend.push_back( E.mkAnd( E.cons( bit_i
	                           , E.cons( divisor[ j ] ) ) ) );
    //
    // Subtract and store in minuend
    //
    Enode * carry = NULL;

    for( unsigned j = 0 ; j < minuend.size( ) ; j++ ) 
    {
      Enode * bit_1 = minuend[ j ];
      Enode * bit_2 = subtrahend[ j ];
      assert( bit_1 );
      assert( bit_2 );

      Enode * bit_2_neg = E.mkNot( E.cons( bit_2 ) );
      Enode * xor_1 = E.mkXor( E.cons( bit_1, E.cons( bit_2_neg ) ) );
      Enode * and_1 = E.mkAnd( E.cons( bit_1, E.cons( bit_2_neg ) ) );

      if ( carry ) 
      {    
	Enode * xor_2 = E.mkXor( E.cons( xor_1, E.cons( carry ) ) );
	Enode * and_2 = E.mkAnd( E.cons( xor_1, E.cons( carry ) ) );
	carry = E.mkOr( E.cons( and_1, E.cons( and_2 ) ) );
	minuend[ j ] = xor_2;
      }    
      else 
      {    
	carry = and_1;
	minuend[ j ] = xor_1;
      }    
    }

    carry = NULL;

    //
    // Adds one, if bit_i is one
    //
    for( unsigned j = 0 ; j < minuend.size( ) ; j++ ) 
    {
      Enode * bit_1 = minuend[ j ];
      Enode * bit_2 = j == 0 ? E.mkTrue( ) : E.mkFalse( );
      assert( bit_1 );
      assert( bit_2 );

      Enode * xor_1 = E.mkXor( E.cons( bit_1, E.cons( bit_2 ) ) );
      Enode * and_1 = E.mkAnd( E.cons( bit_1, E.cons( bit_2 ) ) );

      if ( carry ) 
      {    
	Enode * xor_2 = E.mkXor( E.cons( xor_1, E.cons( carry ) ) );
	Enode * and_2 = E.mkAnd( E.cons( xor_1, E.cons( carry ) ) );
	carry = E.mkOr( E.cons( and_1, E.cons( and_2 ) ) );
	minuend[ j ] = xor_2;
      }    
      else 
      {    
	carry = and_1;
	minuend[ j ] = xor_1;
      }    
    }

    if ( i > 0 )
    {
      //
      // Prepare new minuend
      //
      //                M[i-1]
      //
      // O[2] O[1] O[0]
      //      N[2] N[1] N[0]
      //
      for ( int j = size - 1 ; j >= 1 ; j -- )
	minuend[ j ] = minuend[ j - 1 ];
      minuend[ 0 ] = dividend[ i - 1 ];
    }
    else
    {
      for ( unsigned j = 0 ; j < size ; j ++ )
      {
        (*result)[ j ] = E.mkOr( E.cons( div_eq_zero, E.cons( minuend[ j ] ) ) );
      }
    }
  }

  //
  // Save result and return
  //
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

vector< Enode * > &
BitBlaster::bbBvmul( Enode * e ) 
{ 
  assert( e );
  // assert( e->isBvmul( ) );
  assert( e->getArity( ) == 2 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  vector< Enode * > acc;
  Enode * arg1 = e->get1st( );
  Enode * arg2 = e->get2nd( );
  vector< Enode * > & bb_arg1 = bbEnode( arg1 );
  vector< Enode * > & bb_arg2 = bbEnode( arg2 );
  assert( bb_arg1.size( ) == bb_arg2.size( ) );
  const unsigned size = bb_arg1.size( );
  // Compute term a_{i-1}*b_{j-1} ... a_0*b_0
  for ( unsigned i = 0 ; i < size ; i ++ )
    acc.push_back( E.mkAnd( E.cons( bb_arg2[ 0 ], E.cons( bb_arg1[ i ] ) ) ) );
  // Multi-arity adder
  for ( unsigned i = 1 ; i < size ; i ++ )
  {
    vector< Enode * > addend;
    // Push trailing 0s
    for ( unsigned j = 0 ; j < i ; j ++ )
      addend.push_back( E.mkFalse( ) );
    // Compute term a_{i-1}*b_i ... a_0*b_i 0 ... 0
    for ( unsigned j = 0 ; j < size - i ; j ++ )
      addend.push_back( E.mkAnd( E.cons( bb_arg2[ i ], E.cons( bb_arg1[ j ] ) ) ) );

    assert( addend.size( ) == size );
    // Accumulate computed term
    Enode * carry = NULL;

    for( unsigned k = 0 ; k < size ; k++ ) 
    {
      Enode * bit_1 = acc[ k ];
      Enode * bit_2 = addend[ k ];
      assert( bit_1 );
      assert( bit_2 );

      Enode * xor_1 = E.mkXor( E.cons( bit_1 , E.cons( bit_2 ) ) );
      Enode * and_1 = E.mkAnd( E.cons( bit_1 , E.cons( bit_2 ) ) );

      if ( carry ) 
      {    
	Enode * xor_2 = E.mkXor( E.cons( xor_1 , E.cons( carry ) ) );
	Enode * and_2 = E.mkAnd( E.cons( xor_1 , E.cons( carry ) ) );
	carry = E.mkOr( E.cons( and_1 , E.cons( and_2 ) ) );
	if ( i == size - 1 )
	  result->push_back( xor_2 );
	else
	  acc[ k ] = xor_2;
      }    
      else 
      {    
	carry = and_1;
	if ( i == size - 1 )
	  result->push_back( xor_1 );
	else
	  acc[ k ] = xor_1;
      }    
    }
  }

  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

vector< Enode * > &
BitBlaster::bbSignExtend( Enode * e ) 
{ 
  assert( e );
  // assert( e->isSignExtend( ) );
  assert( e->getArity( ) == 1 );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );


  Enode * x = e->get1st( );
  vector< Enode * > & bb_x = bbEnode( x );
  // Copy x
  unsigned i;
  for ( i = 0 ; i < bb_x.size( ) ; i ++ ) 
    result->push_back( bb_x[ i ] );
  // Sign extend
  for ( ; (int)i < e->getWidth( ) ; i ++ )
    result->push_back( bb_x.back( ) );

  // Save result and return
  bb_cache[ e->getId( ) ] = result;

  return *result;
}

vector< Enode * > &
BitBlaster::bbVar( Enode * e )
{ 
  assert( e );
  assert( e->isVar( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Save variable
  variables.push_back( e );
  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  int width = e->getWidth( );
  // Allocate width new boolean variables
  char def_name[ (e->getCar( )->getName( )).length( ) + 10 ];
  for ( int i = 0 ; i < width ; i ++ )
  {
    sprintf( def_name, "_%s_%d", (e->getCar( )->getName( )).c_str( ), i );
    // E.newSymbol( def_name, DTYPE_BOOL );  
    result->push_back( E.mkVar( def_name ) ); 
  }
  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

vector< Enode * > &
BitBlaster::bbConstant( Enode * e )
{
  assert( e );
  assert( e->isConstant( ) );

  // Return previous result if computed
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  // Allocate new result
  vector< Enode * > * result = new vector< Enode * >;
  // Garbage collect
  garbage.push_back( result );

  if ( e->isTrue( ) )
  {
    result->push_back( E.mkTrue( ) );
  }
  else if ( e->isFalse( ) )
  {
    result->push_back( E.mkFalse( ) );
  }
  else
  {
    unsigned width = e->getWidth( );
    const string value = e->getCar( )->getName( );

    assert( value.length( ) == width );
    for ( unsigned i = 0 ; i < width ; i ++ )
    {
      result->push_back( value[ width - i - 1 ] == '1' 
	  ? E.mkTrue( ) 
	  : E.mkFalse( ) 
	  );
    }
  }
  // Save result and return
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

/*
vector< Enode * > &
BitBlaster::bbUf( Enode * ) 
{ 
  assert( false ); 
}

vector< Enode * > &
BitBlaster::bbUp( Enode * ) 
{ 
  assert( false ); 
}
*/

vector< Enode * > &
BitBlaster::bbDistinct( Enode * e )
{
  assert( e );
  assert( e->isDistinct( ) );
  //
  // Return previous result if computed
  //
  if ( (int)bb_cache.size( ) <= e->getId( ) )
    bb_cache.resize( e->getId( ) + 1, NULL );
  if ( bb_cache[ e->getId( ) ] != NULL )
    return *bb_cache[ e->getId( ) ];

  vector< Enode * > args;

  for ( Enode * ll = e->getCdr( ) 
      ; !ll->isEnil( )
      ; ll = ll->getCdr( ) )
  {
    Enode * arg = ll->getCar( );
    args.push_back( arg );
    assert( args.back( ) );
  } 
  //
  // Quadratic encoding
  //
  vector< Enode * > * result = new vector< Enode * >;
  list< Enode * > res_args;
  for ( size_t i = 0 ; i < args.size( ) - 1 ; i ++ )
  {
    for ( size_t j = i + 1 ; j < args.size( ) ; j ++ )
    {
      vector< Enode * > & bb_pair = bbEnode( E.mkEq( E.cons( args[ i ], E.cons( args[ j ] ) ) ) );
      assert( bb_pair.size( ) == 1 );
      res_args.push_back( E.mkNot( E.cons( bb_pair.back( ) ) ) );
    }
  }

  result->push_back( E.mkAnd( E.cons( res_args ) ) );
  //
  // Garbage collect
  //
  garbage.push_back( result );
  //
  // Save result and return
  //
  bb_cache[ e->getId( ) ] = result;
  return *result;
}

bool 
BitBlaster::addClause ( vec< Lit > & c, Enode * e ) 
{ 
  return solverP.addClause( c, e );
}

//=============================================================================
// CNFization Routines

Var 
BitBlaster::cnfizeAndGiveToSolver( Enode * bb, Enode * atom )
{
  // Stack for unprocessed enodes
  vector< Enode * > unprocessed_enodes; 
  // Cnfize and give to solver
  unprocessed_enodes.push_back( bb );

  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    assert( enode->hasSortBool( ) );
    // 
    // Skip if the node has already been processed before
    //
    if ( (int)cnf_cache.size( ) <= enode->getId( ) )
      cnf_cache.resize( enode->getId( ) + 1, lit_Undef );
    if ( cnf_cache[ enode->getId( ) ] != lit_Undef )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ; 
	  arg_list != E.enil ; 
	  arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push children if not processed already
      //
      if ( (int)cnf_cache.size( ) <= arg->getId( ) )
	cnf_cache.resize( arg->getId( ) + 1, lit_Undef );
      if ( cnf_cache[ arg->getId( ) ] == lit_Undef )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );                      
    Lit result = lit_Undef;
    //
    // At this point, every child has been processed
    //
    //
    // Do the actual cnfization, according to the node type
    //
    if ( enode->isTrue( ) )
      result = constTrue;
    else if ( enode->isFalse( ) )
      result = constFalse;
    else if ( enode->isAtom( ) )
    {
      // Allocate a new boolean variable for this atom
      Var var = solverP.newVar( );
      // Keep track to retrieve model
      assert( cnf_var.find( enode->getId( ) ) == cnf_var.end( ) );
      cnf_var[ enode->getId( ) ] = var;
      result = Lit( var );
    }
    else if ( enode->isNot( ) )
    {
      assert( (int)cnf_cache.size( ) > enode->getId( ) );

      Lit arg_def = cnf_cache[ enode->get1st( )->getId( ) ];       
      assert( arg_def != lit_Undef );
      // Toggle variable
      result = ~arg_def;
    }
    else
    {
      // 
      // Allocates a new variable for definition
      //
      Var var = solverP.newVar( );
      //
      // Store correspondence
      //
      result = Lit( var );
      //
      // Handle remaining cases
      //

      Enode * atom_ = ( enode == bb ? atom : NULL );

      if ( enode->isAnd( ) )
	cnfizeAnd( enode, result, atom_ );
      else if ( enode->isOr( ) )
	cnfizeOr ( enode, result, atom_ );
      /*
      else if ( enode->isIff( ) )
	cnfizeIff( enode, result, atom_ );
      */
      else if ( enode->isXor( ) )
	cnfizeXor( enode, result, atom_ );
      else
	opensmt_error2( "operator not handled ", enode->getCar( ) );
    }

    assert( result != lit_Undef );
    assert( cnf_cache[ enode->getId( ) ] == lit_Undef );
    // Store result 
    cnf_cache[ enode->getId( ) ] = result;
  }

  // 
  // Add an activation variable
  //
  assert( cnf_cache[ bb->getId( ) ] != lit_Undef );

  Lit l = cnf_cache[ bb->getId( ) ];

  Var  act = solverP.newVar( );
  Lit lact = Lit( act );
  vec< Lit > clause;
  //
  // Adds ~act | l
  //
  clause.push( ~lact );
  clause.push( l );
  addClause( clause, atom );
  //
  // Adds act | ~l
  //
  clause.pop( );
  clause.pop( );
  clause.push( lact );
  clause.push( ~l );
  addClause( clause, atom );

  return act;
}

void 
BitBlaster::cnfizeAnd( Enode * enode, Lit def, Enode * atom )
{
  assert( enode );
  Enode * list = NULL;
  //
  // ( a_0 & ... & a_{n-1} ) 
  //
  // <=>
  //
  // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} ) 
  //
  vec< Lit > little_clause;
  vec< Lit > big_clause;
  little_clause.push( ~def );
  big_clause   .push(  def ); 
  for ( list = enode->getCdr( ) 
      ; list != E.enil 
      ; list = list->getCdr( ) )
  {
    Lit arg = cnf_cache[ list->getCar( )->getId( ) ];
    assert( arg != lit_Undef );
    little_clause.push(  arg );
    big_clause   .push( ~arg );  
    addClause( little_clause, atom );
    little_clause.pop( );
  }
  addClause( big_clause, atom );
} 

void 
BitBlaster::cnfizeOr( Enode * enode, Lit def, Enode * atom )
{
  assert( enode );
  Enode * list = NULL;
  //
  // ( a_0 | ... | a_{n-1} ) 
  //
  // <=>
  //
  // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} ) 
  //
  vec< Lit > little_clause;
  vec< Lit > big_clause;
  little_clause.push(  def );
  big_clause   .push( ~def ); 
  for ( list = enode->getCdr( ) 
      ; list != E.enil 
      ; list = list->getCdr( ) )
  {
    Lit arg = cnf_cache[ list->getCar( )->getId( ) ];
    little_clause.push( ~arg );
    big_clause   .push(  arg );  
    addClause( little_clause, atom );
    little_clause.pop( );
  }
  addClause( big_clause, atom );  
} 

void 
BitBlaster::cnfizeXor( Enode * enode, Lit def, Enode * atom )
{
  assert( enode );
  Enode * list = enode->getCdr( );
  //
  // ( a_0 xor a_1 ) 
  //
  // <=>
  //
  // aux = ( -aux |  a_0 | a_1 ) & ( -aux | -a_0 | -a_1 ) &
  //	   (  aux | -a_0 | a_1 ) & (  aux |  a_0 |  a_1 ) 
  //
  assert( list->getArity( ) == 2 );
  Lit arg0 = cnf_cache[ list->getCar( )->getId( ) ];
  Lit arg1 = cnf_cache[ list->getCdr( )->getCar( )->getId( ) ];
  vec< Lit > clause;

  clause.push( ~def );
  
  // First clause
  clause  .push( ~arg0 );
  clause  .push( ~arg1 );
  addClause( clause, atom );
  clause  .pop( );
  clause  .pop( );

  // Second clause
  clause  .push(  arg0 );
  clause  .push(  arg1 );
  addClause( clause, atom ); 
  clause  .pop( );
  clause  .pop( );

  clause.pop( );
  clause.push( def );
  
  // Third clause
  clause  .push( ~arg0 );
  clause  .push(  arg1 );
  addClause( clause, atom ); 
  clause  .pop( );
  clause  .pop( );

  // Fourth clause
  clause  .push(  arg0 );
  clause  .push( ~arg1 );
  addClause( clause, atom ); 
} 

void 
BitBlaster::cnfizeIff( Enode * enode, Lit def, Enode * atom )
{
  assert( enode );
  Enode * list = enode->getCdr( );
  //
  // ( a_0 <-> a_1 ) 
  //
  // <=>
  //
  // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
  //	   (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 ) 
  //
  assert( list->getArity( ) == 2 );
  Lit arg0 = cnf_cache[ list->getCar( )->getId( ) ];
  Lit arg1 = cnf_cache[ list->getCdr( )->getCar( )->getId( ) ];
  vec< Lit > clause;

  clause.push( ~def );
  
  // First clause
  clause  .push(  arg0 );
  clause  .push( ~arg1 );
  addClause( clause, atom );
  clause  .pop( );
  clause  .pop( );

  // Second clause
  clause  .push( ~arg0 );
  clause  .push(  arg1 );
  addClause( clause, atom ); 
  clause  .pop( );
  clause  .pop( );

  clause.pop( );
  clause.push( def );
  
  // Third clause
  clause  .push( ~arg0 );
  clause  .push( ~arg1 );
  addClause( clause, atom ); 
  clause  .pop( );
  clause  .pop( );

  // Fourth clause
  clause  .push(  arg0 );
  clause  .push(  arg1 );
  addClause( clause, atom ); 
}

void 
BitBlaster::cnfizeIfthenelse( Enode * enode, Lit def, Enode * atom )
{
  assert( enode );
  Enode * list = enode->getCdr( );
  //
  // ( if a_0 then a_1 else a_2 ) 
  //
  // <=>
  //
  // aux = ( -aux | -a_0 |  a_1 ) & 
  //       ( -aux |  a_0 |  a_2 ) & 
  //       (  aux | -a_0 | -a_1 ) &
  //       (  aux |  a_0 | -a_2 )
  //
  assert( list->getArity( ) == 2 );
  Lit arg0 = cnf_cache[ list->getCar( )->getId( ) ];
  Lit arg1 = cnf_cache[ list->getCdr( )->getCar( )->getId( ) ];
  vec< Lit > clause;

  clause.push( ~def );
  
  // First clause
  clause  .push( ~arg0 );
  clause  .push(  arg1 );
  addClause( clause, atom );
  clause  .pop( );
  clause  .pop( );

  // Second clause
  clause  .push(  arg0 );
  clause  .push(  arg1 );
  addClause( clause, atom ); 
  clause  .pop( );
  clause  .pop( );

  clause.pop( );
  clause.push( def );
  
  // Third clause
  clause  .push( ~arg0 );
  clause  .push( ~arg1 );
  addClause( clause, atom ); 
  clause  .pop( );
  clause  .pop( );

  // Fourth clause
  clause  .push(  arg0 );
  clause  .push( ~arg1 );
  addClause( clause, atom ); 
}

void
BitBlaster::cleanGarbage( )
{
  while ( !garbage.empty( ) )
  {
    delete garbage.back( );
    garbage.pop_back( );
  }
}

Enode * BitBlaster::simplify( Enode * formula )
{
  assert( formula );

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    // 
    // Skip if the node has already been processed before
    //
    if ( E.valDupMap2( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ; 
	arg_list != E.enil ; 
	arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( E.valDupMap2( arg ) == NULL )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );                      
    Enode * result = NULL;

    if ( enode->isAnd( ) && enode->getArity( ) == 2 )
    {
      Enode * x = E.valDupMap2( enode->get1st( ) );
      Enode * y = E.valDupMap2( enode->get2nd( ) );
      assert( x );
      assert( y );
      //
      // Rule 1
      //
      // (and x (not x)) --> false
      //
      if ( ( x->isNot( ) && x->get1st( ) == y )
	|| ( y->isNot( ) && y->get1st( ) == x ) )
	result = E.mkFalse( );
      //
      // Rule 2
      //
      // (and (not z) (not w)) --> (not (or z w))
      //
      else if ( x->isNot( ) && y->isNot( ) )
      {
	Enode * z = x->get1st( );
	Enode * w = y->get1st( );
	assert( z );
	assert( w );
	result = E.mkNot( E.cons( E.mkOr( E.cons( z, E.cons( w ) ) ) ) );
      }
    }
    else if ( enode->isOr( ) && enode->getArity( ) == 2 )
    {
      Enode * x = E.valDupMap2( enode->get1st( ) );
      Enode * y = E.valDupMap2( enode->get2nd( ) );
      assert( x );
      assert( y );
      //
      // Rule 3
      //
      // (or x (and (not x) z)) --> (or x z))
      //
      if ( y->isAnd( ) 
	&& y->getArity( ) == 2
	&& y->get1st( )->isNot( ) 
	&& y->get1st( )->get1st( ) == x )
      {
	Enode * z = y->get2nd( );
	result = E.mkOr( E.cons( x, E.cons( z ) ) );
      }
      //
      // Rule 4
      //
      // (or (and (not y) z) y) --> (or z y))
      //
      if ( x->isAnd( ) 
	&& x->getArity( ) == 2
	&& x->get1st( )->isNot( ) 
	&& x->get1st( )->get1st( ) == y )
      {
	Enode * z = x->get2nd( );
	result = E.mkOr( E.cons( y, E.cons( z ) ) );
      }
    }

    if ( result == NULL )
      result = E.copyEnodeEtypeTermWithCache( enode, true );

    assert( result );
    assert( E.valDupMap2( enode ) == NULL );
    E.storeDupMap2( enode, result );
  }

  Enode * new_formula = E.valDupMap2( formula );
  assert( new_formula );
  return new_formula;
}

//
// Compute the number of incoming edges for e and children
//
void BitBlaster::computeIncomingEdges( Enode * e, map< int, int > & enodeid_to_incoming_edges )
{
  assert( e );

  if ( !e->isBooleanOperator( ) ) 
    return;

  for ( Enode * list = e->getCdr( ) ; 
        !list->isEnil( ) ; 
	list = list->getCdr( ) )
  {
    Enode * arg = list->getCar( );
    map< int, int >::iterator it = enodeid_to_incoming_edges.find( arg->getId( ) );
    if ( it == enodeid_to_incoming_edges.end( ) )
      enodeid_to_incoming_edges[ arg->getId( ) ] = 1;
    else
      it->second ++;
    computeIncomingEdges( arg, enodeid_to_incoming_edges );
  }
}

//
// Rewrite formula with maximum arity for operators
//
Enode * BitBlaster::rewriteMaxArity( Enode * formula, map< int, int > & enodeid_to_incoming_edges )
{
  assert( formula );

  vector< Enode * > unprocessed_enodes;       // Stack for unprocessed enodes
  unprocessed_enodes.push_back( formula );    // formula needs to be processed
  map< int, Enode * > cache;                  // Cache of processed nodes
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    // 
    // Skip if the node has already been processed before
    //
    if ( cache.find( enode->getId( ) ) != cache.end( ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ; 
	  arg_list != E.enil ; 
	  arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is an unprocessed boolean operator
      //
      if ( arg->isBooleanOperator( ) 
	&& cache.find( arg->getId( ) ) == cache.end( ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
      //
      // If it is an atom (either boolean or theory) just
      // store it in the cache
      //
      else if ( arg->isAtom( ) )
      {
	cache.insert( make_pair( arg->getId( ), arg ) );
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );                      
    Enode * result = NULL;
    //
    // At this point, every child has been processed
    //
    assert ( enode->isBooleanOperator( ) );

    if ( enode->isAnd( ) 
      || enode->isOr ( ) )
    {
      assert( enode->isAnd( ) || enode->isOr( ) );
      //
      // Construct the new lists for the operators
      //
      result = mergeEnodeArgs( enode, cache, enodeid_to_incoming_edges );
    }
    else
    {
      result = enode;
    }

    assert( result );
    assert( cache.find( enode->getId( ) ) == cache.end( ) );
    cache[ enode->getId( ) ] = result;
  }

  Enode * top_enode = cache[ formula->getId( ) ];
  return top_enode;
}

//
// Merge collected arguments for nodes
//
Enode * BitBlaster::mergeEnodeArgs( Enode * e
                                  , map< int, Enode * > & cache
		                  , map< int, int > & enodeid_to_incoming_edges )
{
  assert( e->isAnd( ) || e->isOr( ) );

  Enode * e_symb = e->getCar( );
  vector< Enode * > new_args;
  
  for ( Enode * list = e->getCdr( ) ; 
        !list->isEnil( ) ;
	list = list->getCdr( ) )
  {
    Enode * arg = list->getCar( );
    Enode * sub_arg = cache[ arg->getId( ) ];
    Enode * sym = arg->getCar( );

    if ( sym->getId( ) != e_symb->getId( ) )
    {
      new_args.push_back( sub_arg );
      continue;
    }

    assert( enodeid_to_incoming_edges.find( arg->getId( ) ) != enodeid_to_incoming_edges.end( ) );
    assert( enodeid_to_incoming_edges[ arg->getId( ) ] >= 1 );

    if ( enodeid_to_incoming_edges[ arg->getId( ) ] > 1 )
    {
      new_args.push_back( sub_arg );
      continue;
    }

    for ( Enode * sub_arg_list = sub_arg->getCdr( ) ; 
	  !sub_arg_list->isEnil( ) ; 
	  sub_arg_list = sub_arg_list->getCdr( ) )
      new_args.push_back( sub_arg_list->getCar( ) );
  }

  Enode * new_list = const_cast< Enode * >(E.enil);

  while ( !new_args.empty( ) )
  {
    new_list = E.cons( new_args.back( ), new_list );
    new_args.pop_back( );
  }

  return E.cons( e_symb, new_list );
}

void BitBlaster::computeModel( )
{
  for ( unsigned i = 0 ; i < variables.size( ) ; i++ )
  {
    Enode * e = variables[ i ];
    Real value = 0;
    Real coeff = 1;
    // Retrieve bitblasted vector
    vector< Enode * > & blast = *bb_cache[ e->getId( ) ]; 
    for ( unsigned j = 0 ; j < blast.size( ) ; j ++ )
    {
      Enode * b = blast[ j ];
      if ( cnf_var.find( b->getId( ) ) == cnf_var.end( ) )
	continue;
      Var var = cnf_var[ b->getId( ) ];
      Real bit = solverP.getValue( var ) == l_False ? 0 : 1;
      value = value + coeff * bit;
      coeff = Real( 2 ) * coeff;
    }
    e->setValue( value );
  } 
}
