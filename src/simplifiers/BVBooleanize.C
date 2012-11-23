/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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

#include "BVBooleanize.h"

Enode * BVBooleanize::doit( Enode * formula )
{
  /*
  assert( formula );
  //
  // Step 0: propagate extractions
  //
  formula = propagateExtract( formula );
  //
  // Step 1: replace (= x 0), (= x 1) with type-casts
  //
  formula = replaceWithTypeCasts( formula );
  //
  // Step 2: apply the following rewrite rules:
  //
  // (ite s 1 0) --> s
  // (ite s 0 1) --> (not s)
  // (x + y) = y --> x = 0
  //
  formula = rewriteRules( formula );
  //
  // Step 3: propagate boolcasts
  //
  formula = propagateBoolcast( formula );
  //
  // Step 4: remove type-casts
  //
  formula = removeCasts( formula );
  */
  return formula;
}

Enode * BVBooleanize::propagateExtract( Enode * formula )
{
  /*
  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) 
	; arg_list != egraph.enil 
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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

    int lsb, msb;
    
    if ( enode->isExtract( &msb, &lsb ) && msb == lsb )
    {
      result = propagateExtractRec( egraph.mkExtract( msb, lsb, egraph.valDupMap1( enode->get1st( ) ) ) );
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );

  egraph.doneDupMap1( );
  return new_formula;
  */
  return formula;
}

Enode * BVBooleanize::propagateExtractRec( Enode * e )
{
  /*
  if ( extraction_cache.find( e->getId( ) ) != extraction_cache.end( ) )
    return extraction_cache[ e->getId( ) ];

  int i, j;
  if ( !e->isExtract( &i, &j ) )
    return e;

  const int init_width = e->getWidth( );
  // To fool compiler
  (void)init_width;

  Enode * arg = e->get1st( );
  Enode * res = e;

  int arg_msb, arg_lsb;
  //
  // Apply rewrite rules. We assume x to have width n, y to have width m
  //
  // Rule 1:
  // x[n-1:0] --> x
  //
  if ( arg->getWidth( ) == i - j + 1 )
    res = arg;
  //
  // Rewrite rule for extraction
  //
  // x[msb:lsb][i:j] --> x[i+lsb:j+lsb]
  //
  else if ( arg->isExtract( &arg_msb, &arg_lsb ) )
  {
    Enode * arg_arg = arg->getCdr( )->getCar( );
    assert( !arg_arg->isExtract( ) );
    res = egraph.mkExtract( i + arg_lsb, j + arg_lsb, arg_arg );
    res = propagateExtractRec( res );
  }
  //
  // Rewrite rules for concatenation
  //
  else if ( arg->isConcat( ) )
  {
    list< Enode * > new_args;
    int width_left = arg->getWidth( );

    for ( Enode * list = arg->getCdr( )
	; !list->isEnil( )
	; list = list->getCdr( ) )
    {
      Enode * conc = list->getCar( );
      const int conc_width = conc->getWidth( );
      const int rem_width = width_left - conc_width;
      width_left = rem_width;
      // Compute current extraction indexes
      int real_msb = i - rem_width;
      int real_lsb = j - rem_width;
      // Continue if this slice is out of msb:lsb
      if ( real_msb < 0 || real_lsb >= conc_width )
	continue;
      // Fix indexes if out of bounds
      if ( real_msb >= conc_width ) real_msb = conc_width - 1;
      if ( real_lsb <  0 )          real_lsb = 0;
      // Add slice to list
      new_args.push_front( propagateExtractRec( egraph.mkExtract( real_msb, real_lsb, conc ) ) );
    }

    res = egraph.mkConcat( egraph.cons( new_args ) );
  }
  //
  // Propagate thorugh bitwise operators
  //
  else if ( arg->isBvand( ) 
         || arg->isBvor ( ) 
	 || arg->isBvnot( ) )
  {
    list< Enode * > new_args;
    for ( Enode * list = arg->getCdr( )
	; !list->isEnil( )
	; list = list->getCdr( ) )
    {
      Enode * argarg = list->getCar( );
      new_args.push_front( propagateExtractRec( egraph.mkExtract( i, j, argarg ) ) );
    }
    if ( arg->isBvand( ) )
      res = egraph.mkBvand( egraph.cons( new_args ) );
    else if ( arg->isBvor( ) )
      res = egraph.mkBvor( egraph.cons( new_args ) );
    else if ( arg->isBvnot( ) )
      res = egraph.mkBvnot( egraph.cons( new_args ) );
  }
  //
  // Propagate through ite branches
  //
  else if ( arg->isIte( ) )
  {
    Enode * th = arg->get2nd( );
    Enode * el = arg->get3rd( );
    res = egraph.mkIte( arg->get1st( )
	              , propagateExtractRec( egraph.mkExtract( i, j, th ) )
		      , propagateExtractRec( egraph.mkExtract( i, j, el ) ) );
  }
  //
  // Otherwise normal extraction
  //
  else
  {
    res = egraph.mkExtract( i, j, arg );
  }

  // Initial and final width should match
  assert( res->getWidth( ) == init_width );
  // Check has not been stored already
  assert( extraction_cache.find( e->getId( ) ) == extraction_cache.end( ) );
  // Store
  extraction_cache[ e->getId( ) ] = res;
  return res;
  */
  return e;
}

Enode * BVBooleanize::propagateBoolcast( Enode * formula )
{
  /*
  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) 
	; arg_list != egraph.enil 
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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

    Enode * arg = enode->getArity( ) > 0 ? egraph.valDupMap1( enode->get1st( ) ) : NULL;

    if ( enode->isBoolcast( ) )
    {
      result = propagateBoolcastRec( egraph.mkBoolcast( arg ) );
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );

  egraph.doneDupMap1( );
  return new_formula;
  */
  return formula;
}

Enode * BVBooleanize::propagateBoolcastRec( Enode * e )
{
  /*
  if ( boolcast_cache.find( e->getId( ) ) != boolcast_cache.end( ) )
    return boolcast_cache[ e->getId( ) ];

  if ( !e->isBoolcast( ) )
  {
    assert( e->isSortBool( ) );
    return e;
  }

  Enode * arg = e->get1st( );
  Enode * res = e;
  //
  // (bool (bvnot x)) --> (not (bool x))
  //
  if ( arg->isBvnot( ) )
    res = egraph.mkNot( egraph.cons( propagateBoolcastRec( egraph.mkBoolcast( arg->get1st( ) ) ) ) );
  //
  // (bool (bvand x y)) --> (and (bool x) (bool y))
  //
  else if ( arg->isBvand( ) || arg->isBvor( ) )
  {
    list< Enode * > new_args;
    for ( Enode * list = arg->getCdr( )
	; !list->isEnil( )
	; list = list->getCdr( ) )
    {
      Enode * argarg = list->getCar( );
      new_args.push_front( propagateBoolcastRec( egraph.mkBoolcast( argarg ) ) );
    }
    if ( arg->isBvand( ) )
      res = egraph.mkAnd( egraph.cons( new_args ) ); 
    else
      res = egraph.mkOr ( egraph.cons( new_args ) ); 
  }
  //
  // (bool (word1 x)) --> x
  //
  else if ( arg->isWord1cast( ) )
  {
    res = arg->get1st( );
  }
  //
  // (bool (ite i t e)) --> (if_then_else i (bool t) (bool e))
  //
  else if ( arg->isIte( ) )
  {
    Enode * th = arg->get2nd( );
    Enode * el = arg->get3rd( );
    res = egraph.mkIfthenelse( arg->get1st( )
	                     , propagateBoolcastRec( egraph.mkBoolcast( th ) )
		             , propagateBoolcastRec( egraph.mkBoolcast( el ) ) );
  }
  //
  // (bool (= x y)) --> (= x y)
  //
  else if ( arg->hasSortBool( ) )
  {
    res = arg;
  }
  //
  // Otherwise normal boolcast
  //
  else
  {
    res = egraph.mkBoolcast( arg );
  }

  assert( res->hasSortBool( ) );
  assert( boolcast_cache.find( e->getId( ) ) == boolcast_cache.end( ) );
  boolcast_cache[ e->getId( ) ] = res;
  return res;
  */
  return e;
}

Enode * BVBooleanize::replaceWithTypeCasts( Enode * formula )
{
  /*
  //
  // One, zero shortcuts
  //
  Enode * bv0 = egraph.mkBvnum( const_cast< char * >( "0" ) );
  Enode * bv1 = egraph.mkBvnum( const_cast< char * >( "1" ) );

  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) 
	; arg_list != egraph.enil 
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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
    
    Enode * arg1 = enode->getArity( ) > 0 ? egraph.valDupMap1( enode->get1st( ) ) : NULL;
    Enode * arg2 = enode->getArity( ) > 1 ? egraph.valDupMap1( enode->get2nd( ) ) : NULL;

    // (= x 1) --> boolcast( x )
    if ( enode->isEq( ) && ( arg1 == bv1 || arg2 == bv1 ) )
    {
      result = egraph.mkBoolcast( arg1 == bv1 ? arg2 : arg1 );
    }
    else if ( enode->isEq( ) && ( arg1 == bv0 || arg2 == bv0 ) )
    {
      Enode * cast = egraph.mkBoolcast( arg1 == bv0 ? arg2 : arg1 );
      result = egraph.mkNot( egraph.cons( cast ) );
    }
    else if ( enode->isEq( ) && arg1->getWidth( ) == 1 )
    {
      result = egraph.mkIff( egraph.cons( egraph.mkBoolcast( arg1 )
	                   , egraph.cons( egraph.mkBoolcast( arg2 ) ) ) );
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );

  egraph.doneDupMap1( );
  return new_formula;
  */
  return formula;
}

Enode * BVBooleanize::rewriteRules( Enode * formula )
{
  /*
  //
  // One, zero shortcuts
  //
  Enode * bv0 = egraph.mkBvnum( const_cast< char * >( "0" ) );
  Enode * bv1 = egraph.mkBvnum( const_cast< char * >( "1" ) );

  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) 
	; arg_list != egraph.enil 
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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
    
    Enode * arg1 = enode->getArity( ) > 0 ? egraph.valDupMap1( enode->get1st( ) ) : NULL;
    Enode * arg2 = enode->getArity( ) > 1 ? egraph.valDupMap1( enode->get2nd( ) ) : NULL;
    Enode * arg3 = enode->getArity( ) > 2 ? egraph.valDupMap1( enode->get3rd( ) ) : NULL;

    // ite( s, 0, 1 ) --> s
    if ( enode->isIte( ) && arg2 == bv1 && arg3 == bv0 )
    {
      result = egraph.mkWord1cast( arg1 );
    }
    // ite( s, 1, 0 ) --> (not s)
    else if ( enode->isIte( ) && arg2 == bv0 && arg3 == bv1 )
    {
      result = egraph.mkBvnot( egraph.cons( egraph.mkWord1cast( arg1 ) ) );
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );

  egraph.doneDupMap1( );
  return new_formula;
  */
  return formula;
}

Enode * BVBooleanize::removeCasts( Enode * formula )
{
  /*
  //
  // One, zero shortcuts
  //
  Enode * bv0 = egraph.mkBvnum( const_cast< char * >( "0" ) );
  Enode * bv1 = egraph.mkBvnum( const_cast< char * >( "1" ) );

  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) 
	; arg_list != egraph.enil 
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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
    
    Enode * arg1 = enode->getArity( ) > 0 ? egraph.valDupMap1( enode->get1st( ) ) : NULL;

    // boolCast( x ) --> (= x 1)
    if ( enode->isBoolcast( ) )
    {
      result = egraph.mkEq( egraph.cons( arg1, egraph.cons( bv1 ) ) );
    }
    // wordCast( s ) --> (ite s 1 0)
    else if ( enode->isWord1cast( ) )
    {
      result = egraph.mkIte( arg1, bv1, bv0 );
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );

  egraph.doneDupMap1( );
  return new_formula;
  */
  return formula;
}
