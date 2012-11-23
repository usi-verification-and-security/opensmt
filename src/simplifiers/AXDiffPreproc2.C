/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

#include "AXDiffPreproc2.h"

#define SPLIT_ON_DEMAND_P       0
#define ADD_LIMITED_EQS         0
#define ADD_BIG_AXIOMS          1
#define DONT_ADD_IDX_EQUALITIES 1
//
// TO FIX: 
// - array equalities nel theory solver
// - negated array equalities qua
//

Enode *
AXDiffPreproc2::doit( Enode * formula, const uint64_t )  
{
  assert( formula );
  assert( config.logic == QF_AX );

  // Retrive useful facts indeed
  retrieveTopLevelIndexNeqs( formula );
  // Retrive indexes
  gatherIndexes            ( formula );
  // Canonize to begin with
  formula = canonize       ( formula );
  // Partial flattening
  formula = flatten        ( formula );

  assert( checkFlattened( formula ) );
#if 1
#else
  // Add neq axioms
  formula = addNeqAxioms   ( formula );
#endif
  // Gaussian elimination
  formula = gauss          ( formula );
  assert( checkFlattened( formula ) );
  // Add equalities for rotations
  formula = addEqualities  ( formula );
  // Performs some sort of static learning
  // Seems that it worse performance ...
  formula = addAxioms      ( formula );

  return formula;
}

Enode *
AXDiffPreproc2::addAxioms( Enode * formula )
{
  assert( formula );
  // Gather all top-level read equalities
  egraph.initDup1( );

  vector< Enode * > unprocessed_enodes;
  vector< Enode * > equalities;

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode     = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    const bool arg_is_topl = enode->isAnd( );

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup1( arg ) && arg_is_topl )
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

    if ( enode->isEq( ) )
    {
      Enode * l = enode->get1st( );
      Enode * r = enode->get2nd( );
      if ( l->getRetSort( ) == egraph.getSortElem( ) 
	&& ( l->isSelect( ) || r->isSelect( ) ) )
	equalities.push_back( enode );
    }

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  list< Enode * > axioms;

  //
  // Now that we have all equalities within equalities
  // we do the following. We take reads of the form
  // rd( a, i ) = d
  // rd( a, j ) = e
  // and we say
  // i = j -> d = e
  //
  for ( size_t i = 0 ; i < equalities.size( ) ; i ++ )
  {
    Enode * eq1 = equalities[ i ];

    Enode * sel1 = eq1->get1st( )->isSelect( )
                 ? eq1->get1st( ) 
                 : eq1->get2nd( ) ;
    Enode * var1 = eq1->get1st( )->isVar( )
                 ? eq1->get1st( ) 
                 : eq1->get2nd( ) ;
    Enode * idx1 = sel1->get2nd( );
    for ( size_t j = i + 1 ; j < equalities.size( ) ; j ++ )
    {
      Enode * eq2 = equalities[ j ];

      Enode * sel2 = eq2->get1st( )->isSelect( )
                   ? eq2->get1st( ) 
                   : eq2->get2nd( ) ;

      if ( sel1->get1st( ) != sel2->get1st( ) )
	continue;

      Enode * var2 = eq2->get1st( )->isVar( )
                   ? eq2->get1st( ) 
                   : eq2->get2nd( ) ;

      Enode * idx2 = sel2->get2nd( );

      Enode * idx_eq = egraph.mkEq( egraph.cons( idx1
	                          , egraph.cons( idx2 ) ) );

      Enode * elm_eq = egraph.mkEq( egraph.cons( var1 
	                          , egraph.cons( var2 ) ) );

      axioms.push_back( egraph.mkImplies( egraph.cons( idx_eq
	                                , egraph.cons( elm_eq ) ) ) );
    }
    // 
    // Also for rd( wr( X, i, e ), j ) = d
    // adds i = j -> d = e
    // 
    if ( sel1->get1st( )->isStore( ) )
    {
      Enode * var2 = sel1->get1st( )->get3rd( );
      Enode * idx2 = sel1->get1st( )->get2nd( );
      Enode * idx_eq = egraph.mkEq( egraph.cons( idx1
	                          , egraph.cons( idx2 ) ) );
      Enode * elm_eq = egraph.mkEq( egraph.cons( var1 
	                          , egraph.cons( var2 ) ) );
      axioms.push_back( egraph.mkImplies( egraph.cons( idx_eq
	                                , egraph.cons( elm_eq ) ) ) );
    }
#if ADD_BIG_AXIOMS
    // if ( new_indexes.find( idx1 ) == new_indexes.end( ) )
      // continue;

    // cerr << "FROM: " << equalities[ i ] << endl;

    list< Enode * > prev_eqs;
    Enode * a = sel1->get1st( );
    Enode * e = var1;
    while ( a->isStore( ) )
    {
      Enode * ik = a->get2nd( );
      Enode * eiik = egraph.mkEq( egraph.cons( idx1
	                        , egraph.cons( ik ) ) );
      Enode * negeiik = egraph.mkNot( egraph.cons( eiik ) );

      Enode * ek = a->get3rd( );
      Enode * eeek = egraph.mkEq( egraph.cons( e 
	    , egraph.cons( ek ) ) );

      prev_eqs.push_back( negeiik );
      prev_eqs.push_back( eeek );

      axioms.push_back( egraph.mkOr( egraph.cons( prev_eqs ) ) );

      // cerr << "ADDING: " << axioms.back( ) << endl;

      // Remove last two
      prev_eqs.pop_back( );
      prev_eqs.pop_back( );

      // Add positive eiik
      prev_eqs.push_back( eiik );

      a = a->get1st( );
    }

    Enode * eeek = egraph.mkEq( egraph.cons( e 
			      , egraph.cons( egraph.mkSelect( a, idx1 ) ) ) );
    prev_eqs.push_back( eeek );
    axioms.push_back( egraph.mkOr( egraph.cons( prev_eqs ) ) );
#endif
  }

  axioms.push_back( formula );
  return egraph.mkAnd( egraph.cons( axioms ) );
}

Enode *
AXDiffPreproc2::flatten( Enode * formula )
{
  assert( formula );
  //
  // Flatten what has to be flattened
  //
  egraph.initDupMap1( );

  vector< Enode * > unprocessed_enodes;
  vector< bool > unprocessed_istopl;
  list< Enode * > equalities;

  unprocessed_enodes.push_back( formula );
  unprocessed_istopl.push_back( true );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    assert( unprocessed_enodes.size( ) == unprocessed_istopl.size( ) );
    Enode * enode     = unprocessed_enodes.back( );
    const bool istopl = unprocessed_istopl.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      unprocessed_istopl.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    const bool arg_is_topl = istopl && enode->isAnd( );

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
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
	unprocessed_istopl.push_back( arg_is_topl );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );
    unprocessed_istopl.pop_back( );
    Enode * result = NULL;

    if ( enode->isEq( ) )
    {
      Enode * l = egraph.valDupMap1( enode->get1st( ) );
      Enode * r = egraph.valDupMap1( enode->get2nd( ) );
      // If both variables it's already OK !
      if ( !l->isVar( ) || !r->isVar( ) )
      {
	// Top-level equality, just flatten one side
	if ( istopl )
	{
	  // But only if they are both non-constants
	  if ( !l->isVar( ) && !r->isVar( ) )
	  {
	    Enode * flat_l = getFlat( l, equalities );
	    result = egraph.mkEq( egraph.cons( flat_l
		                , egraph.cons( r ) ) );
	  }
	}
	else 
	{
	  Enode * flat_l = getFlat( l, equalities );
	  Enode * flat_r = getFlat( r, equalities );
	  result = egraph.mkEq( egraph.cons( flat_l
		              , egraph.cons( flat_r ) ) );
	  if ( l->getRetSort( ) == egraph.getSortArray( ) )
#if 1
	    result = addNeqAxiom( flat_l, flat_r, equalities );
#else
	    non_top_array_eqs.insert( result );
#endif
	}
      }
      // Store as non-top-level 
      else if ( !istopl 
	     && l->getRetSort( ) == egraph.getSortArray( ) )
      {
#if 1
	result = addNeqAxiom( l, r, equalities );
#else
	result = egraph.mkEq( egraph.cons( l
	                    , egraph.cons( r ) ) );
	non_top_array_eqs.insert( result );
#endif
      }
    }
    // For store flatten only element
    else if ( enode->isStore( ) )
    {
      Enode * a = egraph.valDupMap1( enode->get1st( ) );
      Enode * i = egraph.valDupMap1( enode->get2nd( ) );
      Enode * e = egraph.valDupMap1( enode->get3rd( ) );
      Enode * flat_e = getFlat( e, equalities );
      result = egraph.mkStore( a, i, flat_e );
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );
  egraph.doneDupMap1( );
  // Canonize introduced reads
  Enode * eqs = canonize( egraph.mkAnd( egraph.cons( equalities ) ) );
  // Conjoin with formula
  Enode * res = egraph.mkAnd( egraph.cons( eqs
	                    , egraph.cons( new_formula ) ) );
  return res;
}

bool
AXDiffPreproc2::checkFlattened( Enode * formula )
{
  assert( formula );
  //
  // Flatten what has to be flattened
  //
  egraph.initDup1( );

  vector< Enode * > unprocessed_enodes;
  vector< bool > unprocessed_istopl;
  list< Enode * > equalities;

  unprocessed_enodes.push_back( formula );
  unprocessed_istopl.push_back( true );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    assert( unprocessed_enodes.size( ) == unprocessed_istopl.size( ) );
    Enode * enode     = unprocessed_enodes.back( );
    const bool istopl = unprocessed_istopl.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      unprocessed_istopl.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    const bool arg_is_topl = istopl && enode->isAnd( );

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup1( arg ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_istopl.push_back( arg_is_topl );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );
    unprocessed_istopl.pop_back( );

    if ( enode->isEq( ) )
    {
      Enode * l = enode->get1st( );
      Enode * r = enode->get2nd( );
      // Top-level equality, just flatten one side
      if ( istopl )
      {
	if ( !l->isVar( ) && !r->isVar( ) )
	{
	  egraph.doneDup1( );
	  return false;
	}
      }
      else
      {
	if ( !l->isVar( ) || !r->isVar( ) )
	{
	  egraph.doneDup1( );
	  return false;
	}
      }
    }
    // For store flatten only element
    else if ( enode->isStore( ) )
    {
      if ( !enode->get3rd( )->isVar( ) )
	return false;
    }

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  return true;
}

Enode *
AXDiffPreproc2::gauss( Enode * formula )
{
  vector< Enode * > arr_eq_list;
  vector< Enode * > elm_eq_list;
  Enode * rest = retrieveTopLevelEqs( formula, arr_eq_list, elm_eq_list );
  if ( !arr_eq_list.empty( ) )
    formula = elimination( rest, arr_eq_list, elm_eq_list );

  return formula;
}

Enode *
AXDiffPreproc2::retrieveTopLevelEqs( Enode * formula
                                   , vector< Enode * > & arr_eq_list 
                                   , vector< Enode * > & elm_eq_list )
{
  list< Enode * >   others;
  vector< Enode * > unprocessed_enodes;

  egraph.initDup1( );

  unprocessed_enodes  .push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    unprocessed_enodes.pop_back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
      continue;

    if ( enode->isAnd( ) )
    {
      Enode * arg_list;
      for ( arg_list = enode->getCdr( )
	  ; arg_list != egraph.enil
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	unprocessed_enodes.push_back( arg );
      }
      continue;
    }
    //
    // Add a new substitution for iff if possible
    //
    if ( enode->isEq( )                                              // Equality
      && enode->get1st( )->getRetSort( ) == egraph.getSortArray( ) ) // of sort array 
    {
      arr_eq_list.push_back( enode );
    }
    else if ( enode->isEq( )                                              // Equality
           && enode->get1st( )->getRetSort( ) == egraph.getSortElem( ) ) // of sort array 
    {
      elm_eq_list.push_back( enode );
    }
    else
    {
      others.push_back( enode );
    }
  }

  egraph.doneDup1( );

  return egraph.mkAnd( egraph.cons( others ) );
}

Enode * AXDiffPreproc2::solveReflexArrayEquations( Enode * formula )
{
  egraph.initDupMap1( );
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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
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

    if ( enode->isEq( ) 
      && enode->get1st( )->getRetSort( ) == egraph.getSortArray( ) )
    {
      Enode * l = enode->get1st( );
      Enode * r = enode->get2nd( );

      vector< Enode * > l_indexes;
      vector< Enode * > r_indexes;
      vector< Enode * > l_elements;
      vector< Enode * > r_elements;

      while ( l->isStore( ) )
      {
	l_indexes.push_back( l->get2nd( ) );
	l_elements.push_back( l->get3rd( ) );
	l = l->get1st( );
      }
      while ( r->isStore( ) )
      {
	r_indexes.push_back( r->get2nd( ) );
	r_elements.push_back( r->get3rd( ) );
	r = r->get1st( );
      }

      if ( l == r )
      {
	Enode * simp = simplifyStoreEq( enode );
	// cerr << "Processing: " << simp << endl;
	list< Enode * > read_eqs;
	Enode * res = solve( simp, read_eqs );
	(void)res;
	assert( res == NULL );
	result = egraph.mkAnd( egraph.cons( read_eqs ) );
	// cerr << "Result    : " << result << endl; 
      }
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * result = egraph.valDupMap1( formula );
  assert( result );
  egraph.doneDupMap1( );

  result = canonize( result );
  
  return result;
}

void
AXDiffPreproc2::retrieveTopLevelIndexNeqs( Enode * formula )
{
  vector< Enode * > unprocessed_enodes;

  egraph.initDup1( );

  unprocessed_enodes  .push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    unprocessed_enodes.pop_back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
      continue;

    if ( enode->isAnd( ) )
    {
      Enode * arg_list;
      for ( arg_list = enode->getCdr( )
	  ; arg_list != egraph.enil
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	unprocessed_enodes.push_back( arg );
      }
      continue;
    }
    //
    // Add a new substitution for iff if possible
    //
    if ( enode->isNot( ) 
      && enode->get1st( )->isEq( )
      && enode->get1st( )->get1st( )->getRetSort( ) == egraph.getSortIndex( ) )      
    {
      top_neg_indexes.insert( enode->get1st( ) );
    }

    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );
}

Enode * 
AXDiffPreproc2::simplifyStoreEq( Enode * e )
{
  assert( e->isEq( ) );
  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  lhs = simplifyStore( lhs );
  rhs = simplifyStore( rhs );
  Enode * simp = egraph.mkEq( egraph.cons( lhs, egraph.cons( rhs ) ) );
  return simp;
}

Enode *
AXDiffPreproc2::simplifyStore( Enode * e )
{
  assert( e->isStore( ) || e->isVar( ) );
  egraph.initDup1( );
  vector< Enode * > useful_stores;
  Enode * a = e;

  while ( a->isStore( ) ) 
  {
    Enode * i = a->get2nd( );
    if ( !egraph.isDup1( i ) )
    {
      useful_stores.push_back( a );
      egraph.storeDup1( i );
    }
    a = a->get1st( );
  }

  Enode * result = a;

  while ( !useful_stores.empty( ) )
  {
    Enode * useful_store = useful_stores.back( );
    useful_stores.pop_back( );
    result = egraph.mkStore( result
	                   , useful_store->get2nd( )
			   , useful_store->get3rd( ) ); 
  }

  egraph.doneDup1( );

  return result;
}

Enode *
AXDiffPreproc2::canonize( Enode * formula )
{
  assert( formula );
  vector< Enode * > unprocessed_enodes;

  egraph.initDupMap2( );

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
    if ( egraph.valDupMap2( enode ) != NULL )
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
      if ( egraph.valDupMap2( arg ) == NULL )
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

    Enode * result = NULL;

#if NEW_MOD_2
    if ( enode->isSelect( ) )
    {
      // Assume arguments are already canonical
      Enode * a = egraph.valDupMap2( enode->get1st( ) );
      Enode * i = egraph.valDupMap2( enode->get2nd( ) );
      result = egraph.mkSelect( a, i );
      result = canonizeTerm( result );
    }
    else if ( enode->isStore( ) )
    {
      Enode * a = egraph.valDupMap2( enode->get1st( ) );
      Enode * i = egraph.valDupMap2( enode->get2nd( ) );
      Enode * e = egraph.valDupMap2( enode->get3rd( ) );
      result = egraph.mkStore( a, i, e );
      result = canonizeTerm( result );
    }
    // TODO: probably useless
    else if ( enode->isEq( ) )
    {
      Enode * l = egraph.valDupMap2( enode->get1st( ) );
      Enode * r = egraph.valDupMap2( enode->get2nd( ) );
      l = canonizeTerm( l );
      r = canonizeTerm( r );
      result = egraph.mkEq( egraph.cons( l, egraph.cons( r ) ) );
    }
#else
    if ( enode->isEq( ) )
    {
      Enode * l = enode->get1st( );
      Enode * r = enode->get2nd( );
      l = canonizeTerm( l );
      r = canonizeTerm( r );
      result = egraph.mkEq( egraph.cons( l, egraph.cons( r ) ) );
    }
#endif

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode, true );

    egraph.storeDupMap2( enode, result );
  }

  Enode * new_formula = egraph.valDupMap2( formula );
  egraph.doneDupMap2( );

  assert( new_formula );

  return new_formula;
}

Enode *
AXDiffPreproc2::canonizeTerm( Enode * assump, set< Enode * > & neg_assump, Enode * t )
{
  Enode * result = NULL;

  // If element equation
  if ( t->isSelect( ) )
  {
    Enode * a = t->get1st( );
    Enode * i = t->get2nd( );
    // Canonize store first
    Enode * innermost_a = simplifyStore( a );
    Enode * element = NULL;
    bool stop = false;
    while( element == NULL 
	&& innermost_a->isStore( ) 
	&& !stop )
    {
      Enode * j = innermost_a->get2nd( );
      Enode * e_ij = egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) );
      // If they are the same, or the same modulo assumption
      if ( j == i || e_ij == assump )
	element = innermost_a->get3rd( );
      // If they are explicitly different
      else if ( neg_assump.find( e_ij ) != neg_assump.end( ) )
      {
	innermost_a = innermost_a->get1st( );
      }
      // Otherwise innermost_a is the term to use
      else
	stop = true;
    }
    // Element found !
    if ( element )
    {
#if NEW_MOD_2
      result = element;
#else
      result = canonizeTerm( element );
#endif
    }
    else
      result = egraph.mkSelect( innermost_a, i );
  }
  else if ( t->isStore( ) )
  {
    assert( false );
  }
  else
    result = t;

  assert( result );

  return result;
}

Enode *
AXDiffPreproc2::canonizeTerm( Enode * t )
{
  Enode * result = NULL;

  // If element equation
  if ( t->isSelect( ) )
  {
    Enode * a = t->get1st( );
    Enode * i = t->get2nd( );
    // Canonize store first
    Enode * innermost_a = simplifyStore( a );
    Enode * element = NULL;
    bool stop = false;
    while( element == NULL 
	&& innermost_a->isStore( ) 
	&& !stop )
    {
      Enode * j = innermost_a->get2nd( );
      // If they are the same
      if ( j == i )
	element = innermost_a->get3rd( );
      // If they are explicitly different
      else if ( top_neg_indexes.find( egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) ) ) != 
	        top_neg_indexes.end( ) )
      {
	innermost_a = innermost_a->get1st( );
      }
      // Otherwise innermost_a is the term to use
      else
	stop = true;
    }
    // Element found !
    if ( element )
    {
      result = canonizeTerm( element );
    }
    else
      result = egraph.mkSelect( innermost_a, i );
  }
  else if ( t->isStore( ) )
  {
    result = simplifyStore( t );
  }
  else
    result = t;

  assert( result );

  return result;
}

Enode *
AXDiffPreproc2::solve( Enode * formula
                     , list< Enode * > & read_eqs )
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 );
#endif
  Enode * eq = formula;

  assert( eq->isEq( ) );
  assert( eq->get1st( )->getRetSort( ) == egraph.getSortArray( ) );
  Enode * lhs = eq->get1st( );
  Enode * rhs = eq->get2nd( );
  Enode * result = NULL;
  bool is_reflex = false;

  // Solve only this case
  Enode * a = lhs;
  vector< Enode * > a_indexes;
  vector< Enode * > a_elements;
  int count_a = 0;
  while( a->isStore( ) ) 
  {
    a_indexes.push_back( a->get2nd( ) );
    a_elements.push_back( a->get3rd( ) );
    a = a->get1st( );
    count_a ++;
  }
  assert( a->isVar( ) );
  Enode * b = rhs;
  vector< Enode * > b_indexes;
  vector< Enode * > b_elements;
  int count_b = 0;
  while( b->isStore( ) ) 
  {
    b_indexes.push_back( b->get2nd( ) );
    b_elements.push_back( b->get3rd( ) );
    b = b->get1st( );
    count_b ++;
  }
  assert( b->isVar( ) );

  is_reflex = a == b;
  if ( !is_reflex )
  {
    if ( count_a < count_b )
    {
      // Constructs a = store( b, ... )
      for ( size_t j = 0 ; j < a_indexes.size( ) ; j ++ )
      {
	// From wr( a, i, e ) to a 
	lhs = lhs->get1st( );
	Enode * sel = egraph.mkSelect( lhs, a_indexes[ j ] );
	Enode * fresh = getFlat( sel, read_eqs );
	read_eqs.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( rhs, a_indexes[ j ] ) 
		          , egraph.cons( a_elements[ j ] ) ) ) );
	// From b to wr( b, i, rd( wr( a, j, e ), i )
	rhs = egraph.mkStore( rhs
	                    , a_indexes[ j ]
	                    , fresh );
      }
      assert( lhs == a );
      result = egraph.mkEq( egraph.cons( lhs, egraph.cons( rhs ) ) ); 
    }
    else
    {
      // Constructs b = store( a, ... )
      for ( size_t j = 0 ; j < b_indexes.size( ) ; j ++ )
      {
	// From wr( b, i, e ) to b
	rhs = rhs->get1st( );
	Enode * sel = egraph.mkSelect( b, b_indexes[ j ] );
	Enode * fresh = getFlat( sel, read_eqs );
	read_eqs.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( lhs, b_indexes[ j ] ) 
		                       , egraph.cons( b_elements[ j ] ) ) ) );
	// From a to wr( a, i, rd( wr( b, j, e ), i )
	lhs = egraph.mkStore( lhs
	                    , b_indexes[ j ]
	                    , fresh );
      }
      assert( rhs == b );
      result = egraph.mkEq( egraph.cons( lhs, egraph.cons( rhs ) ) ); 
    }
  }
  // Solving Reflexive equations
  else
  {
    Enode * saved_lhs = lhs;
    Enode * saved_rhs = rhs;
    // Constructs a = store( b, ... )
    for ( size_t j = 0 ; j < a_indexes.size( ) ; j ++ )
    {
      // From wr( a, i, e ) to a 
      lhs = lhs->get1st( );
      Enode * sel = egraph.mkSelect( lhs, a_indexes[ j ] );
      Enode * fresh = getFlat( sel, read_eqs );
      Enode * eq = egraph.mkEq( egraph.cons( egraph.mkSelect( rhs, a_indexes[ j ] ) 
	                      , egraph.cons( a_elements[ j ] ) ) );
      read_eqs.push_back( canonize( eq ) );
      // From b to wr( b, i, rd( wr( a, j, e ), i )
      rhs = simplifyStore( egraph.mkStore( rhs
	                                 , a_indexes[ j ]
					 , fresh ) );
    }
    assert( lhs == a );
    lhs = saved_lhs;
    rhs = saved_rhs;
    // Constructs b = store( a, ... )
    for ( size_t j = 0 ; j < b_indexes.size( ) ; j ++ )
    {
      // From wr( b, i, e ) to b
      rhs = rhs->get1st( );
      Enode * sel = egraph.mkSelect( rhs, b_indexes[ j ] );
      Enode * fresh = getFlat( sel, read_eqs );
      Enode * eq = egraph.mkEq( egraph.cons( egraph.mkSelect( lhs, b_indexes[ j ] ) 
	    , egraph.cons( b_elements[ j ] ) ) );
      read_eqs.push_back( canonize( eq ) );
      // cerr << "Adding: " << read_eqs.back( ) << endl;
      // From a to wr( a, i, rd( wr( b, j, e ), i )
      lhs = simplifyStore( egraph.mkStore( lhs
	                                 , b_indexes[ j ]
					 , fresh ) );
    }
    assert( rhs == b );
  }

  return result;
}

Enode *
AXDiffPreproc2::elimination( Enode * formula
                           , vector< Enode * > & eq_list 
                           , vector< Enode * > & elm_eq_list 
			   )
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 );
#endif
  list< Enode * > read_eqs;

  for ( size_t i = 0 ; i < elm_eq_list.size( ) ; i ++ )
    read_eqs.push_back( elm_eq_list[ i ] );

  map< Enode *, Enode * > substs;
  //
  // Forward elimination. From the first equality
  // solve and substitute in all others
  //
  for ( size_t i = 0 ; i < eq_list.size( ) ; i ++ )
  {
    assert( eq_list[ i ] );
    assert( eq_list[ i ]->isEq( ) );

    // Canonize eq
    eq_list[ i ] = simplifyStoreEq( eq_list[ i ] );

    // Solve w.r.t. some variable
    // May produce some equality
    // of type Elem

    Enode * a = eq_list[ i ]->get1st( );
    Enode * b = eq_list[ i ]->get2nd( );
    while( a->isStore( ) ) a = a->get1st( );
    while( b->isStore( ) ) b = b->get1st( );

    if ( a == b )
    {
      // Moving in reflex
      // reflex.push_back( eq_list[ i ] );
      Enode * res = solve( eq_list[ i ], read_eqs );
      (void)res;
      assert( res == NULL );
      // Removing from the list
      eq_list[ i ] = NULL;
      continue;
    }

    Enode * res = solve( eq_list[ i ], read_eqs );
    assert( res );

    eq_list[ i ] = simplifyStoreEq( res );

    Enode * lhs = eq_list[ i ]->get1st( );
    Enode * rhs = eq_list[ i ]->get2nd( );

    assert( !lhs->isStore( ) || !rhs->isStore( ) );
    assert( lhs->isVar( ) || rhs->isVar( ) );

    if ( lhs->isVar( ) )
      substs[ lhs ] = rhs;
    else 
      substs[ rhs ] = lhs;

    // Substitute in all equalities down
    for ( size_t j = i + 1 ; j < eq_list.size( ) ; j ++ )
      eq_list[ j ] = substitute( eq_list[ j ], substs );
  }
  //
  // Backward elimination. From the last equality
  // solve substitute in the preceding
  //
  substs.clear( );
  for ( int i = eq_list.size( ) - 1 ; i >= 0 ; i -- )
  {
    // Skip reflex
    if ( eq_list[ i ] == NULL )
      continue;
    // Canonize eq
    eq_list[ i ] = simplifyStoreEq( eq_list[ i ] );
    assert( eq_list[ i ] );
    assert( eq_list[ i ]->isEq( ) );

    Enode * lhs = eq_list[ i ]->get1st( );
    Enode * rhs = eq_list[ i ]->get2nd( );

    assert( !lhs->isStore( ) || !rhs->isStore( ) );
    assert( lhs->isVar( ) || rhs->isVar( ) );

    if ( lhs->isVar( ) )
      substs[ lhs ] = rhs;
    else 
      substs[ rhs ] = lhs;

    // Substitute in all equalities up
    // but skip removed ones
    for ( int j = i - 1 ; j >= 0 ; j -- )
      if ( eq_list[ j ] )
	eq_list[ j ] = substitute( eq_list[ j ], substs );
  }
  //
  // Substitute in reads using all the subts obtained so far
  //
  for ( list< Enode * >::iterator it = read_eqs.begin( )
      ; it != read_eqs.end( )
      ; ++ it )
  {
    *it = canonize( substitute( *it, substs ) );
  }
  //
  // Remove all the substitutions that involve array variables
  // not at the top-level
  //
  for ( set< Enode * >::iterator it = non_top_array_eqs.begin( )
      ; it != non_top_array_eqs.end( ) 
      ; it ++ )
  {
    Enode * a = (*it)->get1st( );
    Enode * b = (*it)->get2nd( );
    map< Enode *, Enode * >::iterator jt = substs.find( a );
    if ( jt != substs.end( ) )
    {
      Enode * rhs = jt->second;
      read_eqs.push_back( egraph.mkEq( egraph.cons( a, egraph.cons( rhs ) ) ) );
      substs.erase( jt );
    }
    jt = substs.find( b );
    if ( jt != substs.end( ) )
    {
      Enode * rhs = jt->second;
      read_eqs.push_back( egraph.mkEq( egraph.cons( b, egraph.cons( rhs ) ) ) );
      substs.erase( jt );
    }
  }

  Enode * new_formula = substitute( formula, substs );

  // And rest with reads
  read_eqs.push_back( new_formula );
  new_formula = egraph.mkAnd( egraph.cons( read_eqs ) );

  // Canonize and return
  return new_formula;
}

Enode *
AXDiffPreproc2::substitute( Enode * formula, map< Enode *, Enode * > & substs )
{
  assert( formula );
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

    map< Enode *, Enode * >::iterator it = substs.find( enode );

    Enode * result = NULL;
    if ( it != substs.end( ) )
    {
      assert( enode->isVar( ) );
      result = it->second;
    }
    else
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( result );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  egraph.doneDupMap1( );

  assert( new_formula );
  return new_formula;
}

Enode * 
AXDiffPreproc2::addNeqAxioms( Enode * formula )
{
  list< Enode * > axioms;
  for ( set< Enode * >::iterator it = non_top_array_eqs.begin( )
      ; it != non_top_array_eqs.end( )
      ; it ++ )
  {
    Enode * l  = (*it)->get1st( );
    Enode * r  = (*it)->get2nd( );
    Enode * eq = (*it);

    // Add axioms
    // (not (= l r)) -> (= (diff l r) i)
    // (not (= l r)) -> (= (select l i) e)
    // (not (= l r)) -> (= (select r i) d)
    // (not (= l r)) -> (not (= d e))
    Enode * diff = egraph.mkDiff( l, r );

    map< Enode *, Enode * >::iterator it = diff_to_ind.find( diff );
    // Diff already seen
    if ( it != diff_to_ind.end( ) )
      continue;

    Enode * ind = freshVarFrom( diff );

    // Store new diff(a,b) = i
    diff_to_ind[ diff ] = ind;

    // Adds to index variables to guess
#if SPLIT_ON_DEMAND_P
    new_indexes.insert( ind );
#else
    index_variables.insert( ind );
#endif
    Enode * sel_l = egraph.mkSelect( l, ind );
    Enode * sel_r = egraph.mkSelect( r, ind );
    Enode * e = freshVarFrom( sel_l );
    Enode * d = freshVarFrom( sel_r );

    /*
    Enode * eq_diff = egraph.mkEq( egraph.cons( diff
	                         , egraph.cons( ind ) ) );
    */

    Enode * eq_sel_l = egraph.mkEq( egraph.cons( sel_l
	                          , egraph.cons( e ) ) );

    Enode * eq_sel_r = egraph.mkEq( egraph.cons( sel_r
	                          , egraph.cons( d ) ) );

    Enode * d_neq_e = egraph.mkNot( egraph.cons( egraph.mkEq( egraph.cons( e
	                                                    , egraph.cons( d ) ) ) ) );

    axioms.push_back( eq_sel_l );
    axioms.push_back( eq_sel_r );

    // a != b -> d != e
    axioms.push_back( egraph.mkOr( egraph.cons( eq
	            , egraph.cons( d_neq_e ) ) ) );
  }

  axioms.push_back( formula );
  Enode * res = egraph.mkAnd( egraph.cons( axioms ) );
  return res;
}

Enode * 
AXDiffPreproc2::addNeqAxiom( Enode * l
                           , Enode * r
			   , list< Enode * > & equalities )
{
  Enode * diff = egraph.mkDiff( l, r );

  map< Enode *, Enode * >::iterator it = diff_to_ind.find( diff );
  Enode * ind = NULL;

  // Diff already seen
  if ( it == diff_to_ind.end( ) )
    ind = freshVarFrom( diff );
  else
    ind = it->second;

  // Store new diff(a,b) = i
  diff_to_ind[ diff ] = ind;

  // Adds to index variables to guess
#if SPLIT_ON_DEMAND_P
#if ADD_LIMITED_EQS
  for ( set< Enode * >::iterator it = index_variables.begin( )
      ; it != index_variables.end( )
      ; it ++ )
  {
    Enode * eq = egraph.mkEq( egraph.cons( (*it)
	  , egraph.cons( ind ) ) );

    cerr << "Adding eq: " << eq << endl;

    char buf[ 32 ];
    sprintf( buf, "ACT_VAR_%d_%d", fresh_count ++, rand( ) % 100 );
    egraph.newSymbol( buf, NULL, sstore.mkBool( ) );
    Enode * av = egraph.mkVar( buf );
    //
    // These two are equivalent to
    // equalities.push_back( egraph.mkIff( egraph.cons( av, egraph.cons( eq ) ) ) );
    //
    equalities.push_back( egraph.mkOr( egraph.cons( egraph.mkNot( egraph.cons( av ) )
	                             , egraph.cons( eq ) ) ) );

    equalities.push_back( egraph.mkOr( egraph.cons( egraph.mkNot( egraph.cons( eq ) )
	                             , egraph.cons( av ) ) ) );
  }
#else
  new_indexes.insert( ind );
#endif
#else
  index_variables.insert( ind );
#endif
  Enode * sel_l = egraph.mkSelect( l, ind );
  Enode * sel_r = egraph.mkSelect( r, ind );
  Enode * e = freshVarFrom( sel_l );
  Enode * d = freshVarFrom( sel_r );

  Enode * eq_sel_l = egraph.mkEq( egraph.cons( sel_l
	                        , egraph.cons( e ) ) );

  Enode * eq_sel_r = egraph.mkEq( egraph.cons( sel_r
	                        , egraph.cons( d ) ) );

  Enode * d_eq_e = egraph.mkEq( egraph.cons( e
	                      , egraph.cons( d ) ) );

  equalities.push_back( eq_sel_l );
  equalities.push_back( eq_sel_r );

  return d_eq_e;
}

Enode * 
AXDiffPreproc2::addEqualities( Enode * formula )
{
  list< Enode * > equalities;
  equalities.push_back( formula );

#if SPLIT_ON_DEMAND_P

#else

#if DONT_ADD_IDX_EQUALITIES
#else

  // Adds equalities between indexes
  for ( set< Enode * >::iterator it = index_variables.begin( )
      ; it != index_variables.end( )
      ; it ++ )
  {
    set< Enode * >::iterator jt = it; jt ++;
    for ( ; jt != index_variables.end( ) ; jt ++ )
    {
      Enode * eq = egraph.mkEq( egraph.cons( (*it)
	                      , egraph.cons( (*jt) ) ) );

      // Different indexes, useless to guess ...
      if ( top_neg_indexes.find( eq ) != top_neg_indexes.end( ) )
	continue;

      // Skip already seen eq
      if ( !eqs_seen.insert( eq ).second )
	continue;

      char buf[ 32 ];
      sprintf( buf, "ACT_VAR_%d_%d", fresh_count ++, rand( ) % 100 );
      egraph.newSymbol( buf, NULL, sstore.mkBool( ) );
      Enode * av = egraph.mkVar( buf );
      //
      // These two are equivalent to
      // equalities.push_back( egraph.mkIff( egraph.cons( av, egraph.cons( eq ) ) ) );
      //
      equalities.push_back( egraph.mkOr( egraph.cons( egraph.mkNot( egraph.cons( av ) )
	                               , egraph.cons( eq ) ) ) );

      equalities.push_back( egraph.mkOr( egraph.cons( egraph.mkNot( egraph.cons( eq ) )
	                               , egraph.cons( av ) ) ) );
    }
  }
#endif

#endif

  /*
  // assert( array_vars.empty( ) );
  gatherArrayVars( formula );

  // Adds equalities of the kind rd(a,i)=e
  for ( set< Enode * >::iterator it = array_vars.begin( ) 
      ; it != array_vars.end( ) 
      ; it ++ )
  {
    for ( set< Enode * >::iterator jt = index_variables.begin( ) 
	; jt != index_variables.end( ) 
	; jt ++ )
    {
      Enode * sel = egraph.mkSelect( *it, *jt );
  
      if ( flat_select.find( sel ) != flat_select.end( ) )
	continue;

      Enode * sel_var = freshVarFrom( sel );
      Enode * eq      = egraph.mkEq( egraph.cons( sel
      	                           , egraph.cons( sel_var ) ) );
      equalities.push_back( eq );
    }
  }
  */

  Enode * res = egraph.mkAnd( egraph.cons( equalities ) );

  return res;
}

Enode *
AXDiffPreproc2::getFlat( Enode * e
                      , list< Enode * > & eq )
{
  if ( e->getArity( ) == 0 )
    return e;

  char def_name[ 32 ];

  map< Enode *, Enode * >::iterator it = definitions.find( e );
  Enode * flat_e = NULL;
  // If l was flattened
  if ( it != definitions.end( ) )
    flat_e = it->second;
  else
  {
    stringstream ss;
    if ( e->getRetSort( ) == egraph.getSortArray( ) )
      ss << "Array";
    else
      ss << e->getRetSort( );
    sprintf( def_name, "%s_%d_%d", ss.str( ).c_str( ), fresh_count ++, rand( ) % 100/*e->getId( )*/ );
    egraph.newSymbol( def_name, NULL, e->getRetSort( ) );
    flat_e = egraph.mkVar( def_name );
    definitions[ e ] = flat_e;
    eq.push_back( egraph.mkEq( egraph.cons( flat_e, egraph.cons( e ) ) ) );
  }
  return flat_e;
}

Enode *
AXDiffPreproc2::freshVarFrom( Enode * e )
{
  char buf[ 32 ];
  stringstream ss;
  ss << e->getRetSort( );
  sprintf( buf, "%s_%d_%d", ss.str( ).c_str( ), fresh_count ++, rand( ) % 100 );
  egraph.newSymbol( buf, NULL, e->getRetSort( ) );
  Enode * var = egraph.mkVar( buf );
  return var;
}

void AXDiffPreproc2::gatherIndexes( Enode * f )
{
  egraph.initDup2( );

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup2( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup2( arg ) )
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

    if ( enode->getRetSort( ) == egraph.getSortIndex( ) 
      && enode->isVar( ) )
    {
      index_variables.insert( enode );
    }

    egraph.storeDup2( enode );
  }

  egraph.doneDup2( );
}

void AXDiffPreproc2::gatherArrayVars( Enode * f )
{
  egraph.initDup2( );

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup2( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup2( arg ) )
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

    if ( enode->isEq( )
      && enode->get1st( )->getRetSort( ) == egraph.getSortArray( ) )
    {
      Enode * a = enode->get1st( );
      Enode * b = enode->get2nd( );
      while ( a->isStore( ) ) a = a->get1st( );
      while ( b->isStore( ) ) b = b->get1st( );
      array_vars.insert( a );
      array_vars.insert( b );
    }

    egraph.storeDup2( enode );
  }

  egraph.doneDup2( );
}
