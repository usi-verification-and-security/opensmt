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

#include "AXDiffPreproc.h"

#define NEW_MOD 1
#define NEW_MOD_2 1
#define NEW_MOD_3 0

Enode *
AXDiffPreproc::doit( Enode * formula
#ifdef PRODUCE_PROOF
		   , const ipartitions_t p 
#endif
		   )  
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 || p != 0 );
  partition = p;
#endif
  assert( formula );
  assert( config.logic == QF_AXDIFF 
       || config.logic == QF_AX );

  // Gaussian elimination only if proof is not required
#ifndef PRODUCE_PROOF
  formula = gauss( formula );
  // egraph.dumpToFile( "aftergauss.smt2", formula );
#endif

  formula = flatten( formula );

#ifdef PRODUCE_PROOF
  // assert( config.produce_inter == 0 
       // || checkPartitions( formula ) );
#endif

  formula = addNeqAxioms( formula );

#ifdef PRODUCE_PROOF
  // assert( config.produce_inter == 0 
       // || checkPartitions( formula ) );

  if ( config.produce_inter != 0 )
    formula = normalizeDiffs( formula );
#endif

  formula = addEqualities ( formula );

#ifdef PRODUCE_PROOF
  // assert( config.produce_inter == 0 
       // || checkPartitions( formula ) );
#endif

  array_eqs_processed = array_eqs.size( );
  // array_vars.clear( );

#ifndef PRODUCE_PROOF
  formula = canonize( formula );
#endif

  return formula;
}

#ifndef PRODUCE_PROOF
Enode *
AXDiffPreproc::gauss( Enode * formula )
{
  // Retrieve i != j at top-level (useful for applying axioms)
  retrieveTopLevelIndexNeqs( formula );
  // A good canonization does not hurt ...
  formula = canonize( formula );
  vector< Enode * > eq_list;
  do
  {
    eq_list.clear( );
    Enode * rest = retrieveTopLevelArrayEqs( formula, eq_list );

    if ( !eq_list.empty( ) )
      formula = elimination( rest, eq_list );
  }
  while( !eq_list.empty( ) );

  // formula = solveReflexArrayEquations( formula );

  return formula;
}

Enode * AXDiffPreproc::instantiateNeq( Enode * l
                                     , Enode * r
				     , list< Enode * > & equalities )
{
  list< Enode * > conj_list;

  for ( set< Enode * >::iterator it = index_variables.begin( )
      ; it != index_variables.end( )
      ; it ++ )
  {
    Enode * ll = canonizeTerm( egraph.mkSelect( l, *it ) );
    Enode * rr = canonizeTerm( egraph.mkSelect( r, *it ) );
    ll = getFlat( ll, equalities );
    rr = getFlat( rr, equalities );
    Enode * eq = egraph.mkEq( egraph.cons( ll
	                    , egraph.cons( rr ) ) );
    conj_list.push_back( eq );
  }

  return egraph.mkAnd( egraph.cons( conj_list ) );
}

Enode * AXDiffPreproc::solveReflexArrayEquations( Enode * formula )
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

Enode *
AXDiffPreproc::retrieveTopLevelArrayEqs( Enode * formula
                                       , vector< Enode * > & eq_list )
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
      /*
      Enode * a = enode->get1st( );
      Enode * b = enode->get2nd( );
      while( a->isStore( ) ) a = a->get1st( );
      while( b->isStore( ) ) b = b->get1st( );
      if ( a != b )
	eq_list.push_back( enode );
      else
	others.push_back( solveReflexArrayEquations( enode ) );
      */
      eq_list.push_back( enode );
    }
    else
    {
      others.push_back( enode );
    }
  }

  egraph.doneDup1( );

  return egraph.mkAnd( egraph.cons( others ) );
}

void
AXDiffPreproc::retrieveTopLevelIndexNeqs( Enode * formula )
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
AXDiffPreproc::simplifyStoreEq( Enode * e )
{
  assert( e->isEq( ) );
  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  lhs = simplifyStore( lhs );
  rhs = simplifyStore( rhs );
  Enode * simp = egraph.mkEq( egraph.cons( lhs, egraph.cons( rhs ) ) );
#ifdef PRODUCE_PROOF
  assignPartitionsFrom( simp, lhs, rhs );
#endif
  return simp;
}

Enode *
AXDiffPreproc::simplifyStore( Enode * e )
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
AXDiffPreproc::canonize( Enode * formula )
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
AXDiffPreproc::canonizeTerm( Enode * assump, set< Enode * > & neg_assump, Enode * t )
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
AXDiffPreproc::canonizeTerm( Enode * t )
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
    result = simplifyStore( t );
  }
  else
    result = t;

  assert( result );

  return result;
}

Enode *
AXDiffPreproc::solve( Enode * formula, list< Enode * > & read_eqs )
{
  // cerr << "Solving: " << formula << endl;
#if 0
  assert( config.produce_inter == 0 );
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

    Enode * result = NULL;

    // Solve only array eqs
    if ( enode->isEq( ) 
      && enode->get1st( )->getRetSort( ) == egraph.getSortArray( ) )
    {
      Enode * lhs = egraph.valDupMap1( enode->get1st( ) );
      Enode * rhs = egraph.valDupMap1( enode->get2nd( ) );

      // Solve only this case
      if ( lhs->isStore( ) 
	&& rhs->isStore( ) )
      {
	Enode * saved_lhs = lhs;
	Enode * saved_rhs = rhs;
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

	if ( a == b )
	{
	  opensmt_error( "Case not handled (yet)" );
	}
	else if ( count_a < count_b )
	{
	  // Constructs a = store( b, ... )
	  for ( size_t j = 0 ; j < a_indexes.size( ) ; j ++ )
	  {
	    Enode * sel = egraph.mkSelect( a, a_indexes[ j ] );
	    Enode * fresh = freshVarFrom( sel );
	    rhs = egraph.mkStore( rhs
		, a_indexes[ j ]
		, fresh );
	    read_eqs.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( saved_rhs, a_indexes[ j ] ) 
		                           , egraph.cons( a_elements[ j ] ) ) ) );
	    read_eqs.push_back( egraph.mkEq( egraph.cons( sel
		                           , egraph.cons( fresh ) ) ) );
	  }
	  lhs = a;

	  result = egraph.mkEq( egraph.cons( lhs, egraph.cons( rhs ) ) ); 
	}
	else
	{
	  // Constructs b = store( a, ... )
	  for ( size_t j = 0 ; j < b_indexes.size( ) ; j ++ )
	  {
	    Enode * sel = egraph.mkSelect( b, b_indexes[ j ] );
	    Enode * fresh = freshVarFrom( sel );
	    lhs = egraph.mkStore( lhs
		, b_indexes[ j ]
		, fresh );
	    read_eqs.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( saved_lhs, b_indexes[ j ] ) 
		                           , egraph.cons( b_elements[ j ] ) ) ) );
	    read_eqs.push_back( egraph.mkEq( egraph.cons( sel
		                           , egraph.cons( fresh ) ) ) );
	  }
	  rhs = b;
	  result = egraph.mkEq( egraph.cons( lhs, egraph.cons( rhs ) ) ); 
	}
      }
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  egraph.doneDupMap1( );

  assert( new_formula );
  return new_formula;
#else
  assert( config.produce_inter == 0 );
  Enode * eq = formula;

  assert( eq->isEq( ) );
  assert( eq->get1st( )->getRetSort( ) == egraph.getSortArray( ) );
  Enode * lhs = eq->get1st( );
  Enode * rhs = eq->get2nd( );
  Enode * result = NULL;
  bool is_reflex = false;

  // Solve only this case
  /*
  if ( lhs->isStore( ) 
    && rhs->isStore( ) )
  {
  */
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
	  // Enode * fresh = freshVarFrom( sel );
	  read_eqs.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( rhs, a_indexes[ j ] ) 
		  , egraph.cons( a_elements[ j ] ) ) ) );
	  // From b to wr( b, i, rd( wr( a, j, e ), i )
	  rhs = egraph.mkStore( rhs
	      , a_indexes[ j ]
	      , sel );
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
	  // Enode * fresh = freshVarFrom( sel );
	  read_eqs.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( lhs, b_indexes[ j ] ) 
		  , egraph.cons( b_elements[ j ] ) ) ) );
	  // From a to wr( a, i, rd( wr( b, j, e ), i )
	  lhs = egraph.mkStore( lhs
	      , b_indexes[ j ]
	      , sel );
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
	// Enode * fresh = freshVarFrom( sel );
	Enode * eq = egraph.mkEq( egraph.cons( egraph.mkSelect( rhs, a_indexes[ j ] ) 
		                , egraph.cons( a_elements[ j ] ) ) );
	read_eqs.push_back( canonize( eq ) );
	// From b to wr( b, i, rd( wr( a, j, e ), i )
	rhs = simplifyStore( egraph.mkStore( rhs, a_indexes[ j ], sel ) );
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
	// Enode * fresh = freshVarFrom( sel );
	Enode * eq = egraph.mkEq( egraph.cons( egraph.mkSelect( lhs, b_indexes[ j ] ) 
	  	                , egraph.cons( b_elements[ j ] ) ) );
	read_eqs.push_back( canonize( eq ) );
	// cerr << "Adding: " << read_eqs.back( ) << endl;
	// From a to wr( a, i, rd( wr( b, j, e ), i )
	lhs = simplifyStore( egraph.mkStore( lhs, b_indexes[ j ], sel ) );
      }
      assert( rhs == b );
    }
  /*
  }

  if ( result )
  {
    cerr << "result: " << result << endl;
  }
  else
  {
    cerr << "REFLEX" << endl;
  }
  */

  return result;
#endif
}

Enode *
AXDiffPreproc::elimination( Enode * formula
                          , vector< Enode * > & eq_list 
			  )
{
  assert( config.produce_inter == 0 );
  list< Enode * > read_eqs;
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

  /*
  // Add formula
  reflex.push_back( formula );
  formula = egraph.mkAnd( egraph.cons( reflex ) );
  */

  // Substitute using all substitutions obtained so far
  Enode * new_formula = substitute( formula, substs );
  for ( list< Enode * >::iterator it = read_eqs.begin( )
      ; it != read_eqs.end( )
      ; ++ it )
  {
    *it = substitute( *it, substs );
  }

  // And rest with reads
  read_eqs.push_back( new_formula );
  new_formula = egraph.mkAnd( egraph.cons( read_eqs ) );

  // Canonize and return
  return canonize( new_formula );
}

Enode *
AXDiffPreproc::substitute( Enode * formula, map< Enode *, Enode * > & substs )
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
AXDiffPreproc::substitute2( Enode * formula, map< Enode *, Enode * > & substs )
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

    map< Enode *, Enode * >::iterator it = substs.find( enode );

    Enode * result = NULL;
    if ( it != substs.end( ) )
    {
      assert( enode->isVar( ) );
      result = it->second;
    }
    else
      result = egraph.copyEnodeEtypeTermWithCache( enode, true );

    assert( result );
    egraph.storeDupMap2( enode, result );
  }

  Enode * new_formula = egraph.valDupMap2( formula );
  egraph.doneDupMap2( );

  assert( new_formula );
  return new_formula;
}
#endif

Enode *
AXDiffPreproc::flatten( Enode * formula )
{
  // Step 1: figure out already flat constraints,
  // which are those equalities at top-level of
  // the kind c = t, with c constant and t term
  // of depth 1
  assert( formula );

#if NEW_MOD
  gatherIndexes( formula );
#endif

  list< Enode * > equalities;
  list< Enode * > yet_not_flat;
  egraph.initDup1( );
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
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    if ( enode->isAnd( ) )
    {
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
	  unprocessed_children = true;
	}
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    if ( enode->isEq( ) 
      || ( enode->isNot( ) 
        && enode->get1st( )->isEq( ) ) )
    {
      Enode * eq = enode->isNot( ) 
	         ? enode->get1st( ) 
		 : enode;
      const bool is_neq = enode->isNot( );
      Enode * l = eq->get1st( );
      Enode * r = eq->get2nd( );

      bool is_flat = false;
      if ( is_neq && ( !l->isVar( ) || !r->isVar( ) ) )
      {
	yet_not_flat.push_back( enode );
	assert( !egraph.isDup1( enode ) );
	egraph.storeDup1( enode );
	continue;
      }

      // At least one is variable
      if ( l->isVar( ) || r->isVar( ) )
      {
#if NEW_MOD
	is_flat = true;
#else
	if ( l->getRetSort( ) == egraph.getSortArray( ) )
	{
	  is_flat = true;
	  while( l->isStore( ) && is_flat ) 
	  {
	    is_flat = l->get2nd( )->isVar( )
	           && l->get3rd( )->isVar( );
	    l = l->get1st( );
	  }
	  while( r->isStore( ) && is_flat ) 
	  {
	    is_flat = r->get2nd( )->isVar( )
	           && r->get3rd( )->isVar( );
	    r = r->get1st( );
	  }
	  if ( is_neq )
	  {
	    is_flat = l->isVar( ) && r->isVar( );
	    array_eqs.push_back( enode->get1st( ) );
	  }
	}
	else 
	{
	  is_flat = true;
	  vector< Enode * > unprocessed_args;
	  unprocessed_args.push_back( l );
	  unprocessed_args.push_back( r );
	  while ( !unprocessed_args.empty( ) && is_flat )
	  {
	    Enode * arg = unprocessed_args.back( );
	    unprocessed_args.pop_back( );

	    if ( arg->isStore( ) )
	    {
	      unprocessed_args.push_back( arg->get1st( ) );
	      unprocessed_args.push_back( arg->get2nd( ) );
	      unprocessed_args.push_back( arg->get3rd( ) );
	    }
	    else if ( arg->isSelect( ) )
	    {
	      if ( arg != l && arg != r ) 
		is_flat = false; 
	      else
	      {
		unprocessed_args.push_back( arg->get1st( ) );
		unprocessed_args.push_back( arg->get2nd( ) );
	      }
	    }
	  }
	}
#endif
      }

      if ( is_flat )
      {
	equalities.push_back( enode );

	// We do not do this optimization
	// when interpolation is enabled
	if ( enode->isEq( )
	  && enode->get1st( )->getRetSort( ) == egraph.getSortElem( ) 
	  && config.produce_inter == 0 )
	{
	  Enode * l = enode->get1st( );
	  Enode * r = enode->get2nd( );
	  if ( l->isSelect( ) || r->isSelect( ) )
	  {
	    assert( !l->isSelect( ) || !r->isSelect( ) );
	    if ( l->isSelect( ) )
	      flat_select.insert( l );
	    if ( r->isSelect( ) )
	      flat_select.insert( r );
	  }
	}

#if NEW_MOD
#else
	gatherIndexes( enode );
#endif
      }
      else
	yet_not_flat.push_back( enode );
    }
    else if ( !enode->isAnd( ) )
      yet_not_flat.push_back( enode );

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0 
    && !yet_not_flat.empty( ) )
    opensmt_error( "Currently, we accept only flat constraints for interpolation" );
#endif

  //
  // Flatten what has to be flattened
  //

  formula = egraph.mkAnd( egraph.cons( yet_not_flat ) );

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

#if NEW_MOD
    if ( enode->isEq( ) )
    {
      Enode * l = egraph.valDupMap1( enode->get1st( ) );
      Enode * r = egraph.valDupMap1( enode->get2nd( ) );
      //
      // Equality is of the kind
      // select = select, or
      // store = store, or
      // var = store for negated eqs. Create a variable to separate
      //
#if 0 && NEW_MOD_2
      if ( l->isStore( ) && r->isStore( ) )
      {
	set< Enode * > neg_assumptions;
	Enode * eq = egraph.mkEq( egraph.cons( l, egraph.cons( r ) ) );
	result = simplifyEq( neg_assumptions, eq, equalities );
	cerr << "Rewriting: " << eq << endl;
	cerr << "     Into: " << result << endl;
      }
      else
      {
	Enode * sep = getFlat( l, equalities );
	//
	// Produce second equality
	//
	result = egraph.mkEq( egraph.cons( sep
	      , egraph.cons( r ) ) );
	if ( l->isStore( ) || r->isStore( ) )
	  array_eqs.push_back( result );
      }
#else
      if( l->isSelect( ) )
      {
	Enode * sep = getFlat( l, equalities );
	//
	// Produce second equality
	//
	result = egraph.mkEq( egraph.cons( sep
	                    , egraph.cons( r ) ) );
      }
      else
      {
#if NEW_MOD_3
	Enode * a = l;
	Enode * b = r;
	while ( a->isStore( ) ) a = a->get1st( );
	while ( b->isStore( ) ) b = b->get1st( );
	if ( a == b )
	{
	  result = instantiateNeq( l, r, equalities );
	}
	else
	{
	  assert( l->isStore( ) || r->isStore( ) );

	  Enode * flat_l = getFlat( l, equalities );
	  Enode * flat_r = getFlat( r, equalities );
	  result = egraph.mkEq( egraph.cons( flat_l
		              , egraph.cons( flat_r ) ) );
	  array_eqs.push_back( result );
	}
#else
	assert( l->isStore( ) || r->isStore( ) );

	Enode * flat_l = getFlat( l, equalities );
	Enode * flat_r = getFlat( r, equalities );
	result = egraph.mkEq( egraph.cons( flat_l
	                    , egraph.cons( flat_r ) ) );
	array_eqs.push_back( result );
#endif
      }
#endif
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }
#else
    if ( enode->isStore( ) )
    {
      Enode * a = egraph.valDupMap1( enode->get1st( ) );
      Enode * i = egraph.valDupMap1( enode->get2nd( ) );
      Enode * e = egraph.valDupMap1( enode->get3rd( ) );
      // Store indexes in writes
      // write_indexes.insert( i );
      // Assume i already flat
      assert( i->getArity( ) == 0 );
      // Do not flatten a
      Enode * flat_a = a;
      Enode * flat_e = getFlat( e, equalities );
      assert( flat_e );
      result = egraph.mkStore( flat_a, i, flat_e );
    }
    else if ( enode->isSelect( ) )
    {
      Enode * a = egraph.valDupMap1( enode->get1st( ) );
      Enode * i = egraph.valDupMap1( enode->get2nd( ) );
      // Assume i already flat
      assert( i->getArity( ) == 0 );
      Enode * flat_a = a;
      result = egraph.mkSelect( flat_a, i );
    }
    else 
    if ( enode->isDiff( ) )
    {
      assert( config.logic == QF_AXDIFF );
      Enode * a = egraph.valDupMap1( enode->get1st( ) );
      Enode * b = egraph.valDupMap1( enode->get2nd( ) );

      Enode * flat_a = getFlat( a, equalities );
      Enode * flat_b = getFlat( b, equalities );
      // Store array_vars

      assert( flat_b );
      assert( flat_a );
      result = egraph.mkDiff( flat_a, flat_b );
      index_variables.insert( getFlat( result, equalities ) );
    }
    // Flatten all but those array equalities which are at top-level
    else if ( enode->isEq( ) )
    {
      Enode * l = egraph.valDupMap1( enode->get1st( ) );
      Enode * r = egraph.valDupMap1( enode->get2nd( ) );

      assert( !l->isStore( ) || r->isStore( ) );

      Enode * flat_l = l; 
      Enode * flat_r = r; 

      if ( l->getRetSort( ) != egraph.getSortArray( ) )
      {
	if ( !l->isVar( ) && !r->isVar( ) )
	{
	  flat_l = getFlat( l, equalities );
	  flat_r = getFlat( r, equalities );
	}
      }
      // Equality of sort array
      else 
      {
	flat_l = getFlat( l, equalities );
	flat_r = getFlat( r, equalities );
      }

      assert( result == NULL );
      result = egraph.mkEq( egraph.cons( flat_l
	                  , egraph.cons( flat_r ) ) );

      if ( l->getRetSort( ) == egraph.getSortArray( ) )
      {
	array_eqs.push_back( result );
      }

      gatherIndexes( enode );
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }
#endif

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );
  egraph.doneDupMap1( );
  equalities.push_back( new_formula );
  Enode * res = egraph.mkAnd( egraph.cons( equalities ) );
  return res;
}

Enode * 
AXDiffPreproc::addNeqAxioms( Enode * formula )
{
  list< Enode * > axioms;
  for ( size_t i = array_eqs_processed ; i < array_eqs.size( ) ; i ++ )
  {
    Enode * l  = array_eqs[ i ]->get1st( );
    Enode * r  = array_eqs[ i ]->get2nd( );
    Enode * eq = array_eqs[ i ];

#if NEW_MOD_2
#else
    while( l->isStore( ) ) l = l->get1st( );
    while( r->isStore( ) ) r = r->get1st( );
    assert( l->isVar( ) );
    assert( r->isVar( ) );
    assert( l != r );
#endif

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
    index_variables.insert( ind );
    Enode * sel_l = egraph.mkSelect( l, ind );
    Enode * sel_r = egraph.mkSelect( r, ind );
    Enode * e = freshVarFrom( sel_l );
    Enode * d = freshVarFrom( sel_r );

    Enode * eq_diff = egraph.mkEq( egraph.cons( diff
	  , egraph.cons( ind ) ) );

    Enode * eq_sel_l = egraph.mkEq( egraph.cons( sel_l
	  , egraph.cons( e ) ) );

    Enode * eq_sel_r = egraph.mkEq( egraph.cons( sel_r
	  , egraph.cons( d ) ) );

    Enode * d_neq_e = egraph.mkNot( egraph.cons( 
	  egraph.mkEq( egraph.cons( e
	      , egraph.cons( d ) ) ) ) );

    // Conditional axiom a!=b -> diff(a,b) = i
    axioms.push_back( egraph.mkOr( egraph.cons( eq
	            , egraph.cons( eq_diff ) ) ) );
    // Conditional axiom a!=b -> rd
    axioms.push_back( egraph.mkOr( egraph.cons( eq
	            , egraph.cons( eq_sel_l ) ) ) );
    // Conditional axiom a!=b -> rd
    axioms.push_back( egraph.mkOr( egraph.cons( eq
	            , egraph.cons( eq_sel_r ) ) ) );
    // Pushed at top-level !!
    // axioms.push_back( eq_diff );
    // axioms.push_back( eq_sel_l );
    // axioms.push_back( eq_sel_r );
    // Conditional axiom a!=b -> d!=e
    axioms.push_back( egraph.mkOr( egraph.cons( eq
	            , egraph.cons( d_neq_e ) ) ) );
  }

  axioms.push_back( formula );
  Enode * res = egraph.mkAnd( egraph.cons( axioms ) );
  return res;
}

Enode * 
AXDiffPreproc::addEqualities( Enode * formula )
{
  list< Enode * > equalities;
  equalities.push_back( formula );

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

      // Make sure we do not create mixed equalities
#ifdef PRODUCE_PROOF
      if ( config.produce_inter != 0
	&& eq->getIPartitions( ) == 1 )
	continue;
#endif

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
#ifdef PRODUCE_PROOF
      av->setIPartitions( partition );
#endif
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

  // assert( array_vars.empty( ) );
  gatherArrayVars( formula );

  // Adds equalities of the kind rd(a,i)=e
  for ( set< Enode * >::iterator it = array_vars.begin( ) 
      ; it != array_vars.end( ) 
      ; it ++ )
  {
#ifdef PRODUCE_PROOF
    // Skip arrays that are local to one partition
    // ABcommon should be processed instead
    if ( ( (*it)->getIPartitions( ) 
         & partition ) == 0 )
      continue;
#endif

    for ( set< Enode * >::iterator jt = index_variables.begin( ) 
	; jt != index_variables.end( ) 
	; jt ++ )
    {
      Enode * sel = egraph.mkSelect( *it, *jt );

#ifdef PRODUCE_PROOF
      if ( config.produce_inter != 0 
	&& sel->getIPartitions( ) == 1 )
	continue;
#endif
  
      if ( flat_select.find( sel ) != flat_select.end( ) )
	continue;

      Enode * sel_var = freshVarFrom( sel );
      Enode * eq      = egraph.mkEq( egraph.cons( sel
      	                           , egraph.cons( sel_var ) ) );
      equalities.push_back( eq );
    }
  }

  Enode * res = egraph.mkAnd( egraph.cons( equalities ) );
  return res;
}

Enode *
AXDiffPreproc::getFlat( Enode * e
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
AXDiffPreproc::freshVarFrom( Enode * e )
{
  char buf[ 32 ];
  stringstream ss;
  ss << e->getRetSort( );
  sprintf( buf, "%s_%d_%d", ss.str( ).c_str( ), fresh_count ++, rand( ) % 100 );
  egraph.newSymbol( buf, NULL, e->getRetSort( ) );
  Enode * var = egraph.mkVar( buf );
  return var;
}

void AXDiffPreproc::gatherIndexes( Enode * f )
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

void AXDiffPreproc::gatherArrayVars( Enode * f )
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

#if 0
// SimplifyStoreEq( a, b )
//
// if ( a = b ) return true;
//
// if ( a->isStore( ) && b->isStore( ) )
//  a = wr( a', i, e )
//  b = wr( b', j, d )
//  return (i = j -> e = d) and 
//         (i != j -> (rd( a', j ) = d and rd( b', i ) and SimplifyStoreEq( a', b' )) 

#if 1
Enode * AXDiffPreproc::simplifyEq( set< Enode * > & neg_assumptions
                                 , Enode * eq
				 , list< Enode * > & equalities )
{
  assert( eq );

  if ( eq->isTrue( ) )
    return eq;

  Enode * a = eq->get1st( );
  Enode * b = eq->get2nd( );

  if ( a == b ) return egraph.mkTrue( );

  cerr << "CALLING ON : " << a << " = " << b << endl;
  cerr << " with ass  : " << endl;
  for ( set< Enode * >::iterator it = neg_assumptions.begin( ) 
      ; it != neg_assumptions.end( )
      ; it ++ )
  {
    cerr << "     not " << *it << endl;
  }

  if ( a->isStore( ) && b->isStore( ) )
  {
    Enode * ap = a->get1st( );
    Enode * i  = a->get2nd( );
    Enode * e  = a->get3rd( );
    Enode * bp = b->get1st( );
    Enode * j  = b->get2nd( );
    Enode * d  = b->get3rd( );

    Enode * assump = egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) );

    map< Enode *, Enode * > substs;
    substs[ i ] = j;

    e = canonizeTerm( substitute2( e, substs ) );
    d = canonizeTerm( substitute2( e, substs ) );

    if ( e != d )
    {
      e = getFlat( e, equalities );
      d = getFlat( d, equalities );
    }

    Enode * elm_eq = egraph.mkEq( egraph.cons( e
	                        , egraph.cons( d ) ) );

    list< Enode * > conj1_impl_list;
    conj1_impl_list.push_back( assump );
    conj1_impl_list.push_back( elm_eq );

    Enode * conj1 = NULL;
    bool split = false;
    if ( neg_assumptions.insert( assump ).second )
    {
      split = true;
      Enode * simp_eq = canonize( substitute2( eq, substs ) );

      cerr << "ass      : " << assump << endl;
      cerr << "elm_eq   : " << elm_eq << endl;
      cerr << "can eq : " << simp_eq << endl;

      if ( simp_eq->isEq( ) )
      {
	Enode * ll = simp_eq->get1st( );
	Enode * rr = simp_eq->get2nd( );
	if ( ll->isStore( ) && rr->isStore( ) )
	{
	  simp_eq = egraph.mkEq( egraph.cons( ll->get1st( ), egraph.cons( rr->get1st( ) ) ) );
	  simp_eq = simplifyEq( neg_assumptions
		              , simp_eq
		              , equalities );
	}
      }
      conj1_impl_list.push_back( simp_eq );
      conj1 = egraph.mkImplies( egraph.cons( conj1_impl_list ) );
      cerr << "Conj1 is : " << conj1 << endl;
    }
    // Assumption does not hold, so implication is true
    else
    {
      cerr << "Skipping conj1, assumption can't hold" << endl;
      conj1 = egraph.mkTrue( );
    }

    list< Enode * > conj2_impl_list;
    
    Enode * rd1 = canonizeTerm( assump, neg_assumptions, egraph.mkSelect( ap, j ) );
    Enode * rd2 = canonizeTerm( assump, neg_assumptions, egraph.mkSelect( bp, i ) );

    // cerr << "elm_eq : " << elm_eq << endl;
    // cerr << "rd1    : " << rd1 << endl;
    // cerr << "rd2    : " << rd2 << endl;

    Enode * ss  = simplifyEq( neg_assumptions
	                    , egraph.mkEq( egraph.cons( ap, egraph.cons( bp ) ) ) 
			    , equalities
			    ); 

    if ( rd1 != rd2 )
    {
      rd1 = getFlat( rd1, equalities );
      rd2 = getFlat( rd2, equalities );
    }

    conj2_impl_list.push_back( egraph.mkEq( egraph.cons( rd1, egraph.cons( rd2 ) ) ) );

    // cerr << "eq: " << conj2_impl_list.back( ) << endl;

    conj2_impl_list.push_back( ss );

    Enode * conj2_impl = egraph.mkAnd( egraph.cons( conj2_impl_list ) );

    if ( !split )
    {
      // cerr << "Assumption " << assump << " cannot be taken" << endl;
      Enode * result = conj2_impl;
      cerr << "Conj2 alone is : " << result << endl;
      return result;
    }

    Enode * conj2 = egraph.mkImplies( egraph.cons( egraph.mkNot( egraph.cons( assump ) )
	                            , egraph.cons( conj2_impl ) ) );

    cerr << "Conj2 is : " << conj2 << endl;

    Enode * result = egraph.mkAnd( egraph.cons( conj1, egraph.cons( conj2 ) ) );
    // cerr << "RESULT: " << result << endl;
    return result;
  }

  return eq;
}
#else
Enode * AXDiffPreproc::simplifyEq( Enode * eq )
{
  assert( eq );
  Enode * l = eq->get1st( );
  Enode * r = eq->get2nd( );
  assert( l );
  assert( r );
  vector< Enode * > indexes_l, indexes_r;
  vector< Enode * > elem_l, elem_r;
  while( l->isStore( ) )
  {
    indexes_l.push_back( l->get2nd( ) );
    elem_l.push_back( l->get3rd( ) );
    l = l->get1st( );
  } 
  while( r->isStore( ) )
  {
    indexes_r.push_back( r->get2nd( ) );
    elem_r.push_back( r->get3rd( ) );
    r = r->get1st( );
  } 

  // TODO: can be actually generalized ...
  if ( l != r ) 
    return eq;
  // TODO: can be actually generalized ...
  if ( indexes_l.size( ) != indexes_r.size( ) )
    return eq;

  list< Enode * > axioms;
  list< Enode * > idx_hyp;

  cerr << "Considering eq: " << eq << endl;

  // wr( wr( a, i1, d1 ), i2, d2 ) = wr( wr( a, j1, e1 ), j2, e2 )
  //
  //                              <->
  //
  //    (i2  = j2) -> d2 = e2
  // /\ (i2 != j2) -> rd( wr( wr( a, i1, d1 ), i2, d2 ), j2 ) = rd( wr( wr( a, j1, e1 ), j2, e2 ), i2 )
  //                  [rd( wr( a, i1, d1 ), j2 ) )            = rd( wr( a, j1, e1 ), i2 )]

  // Let's see what happens by making hypothesis
  for ( size_t i = 0 ; i < indexes_l.size( ) ; i ++ )
  {
    // produce ik = jk
    Enode * idx_eq = egraph.mkEq( egraph.cons( indexes_l[ i ]
	                        , egraph.cons( indexes_r[ i ] ) ) );
    // Conjoin with prev hyps
    idx_hyp.push_back( idx_eq );
    Enode * hyp = egraph.mkAnd( egraph.cons( idx_hyp ) );

    map< Enode *, Enode * > substs;
    substs[ indexes_l[ i ] ] = indexes_r[ i ];

    Enode * elm_eq = egraph.mkEq( egraph.cons( elem_l[ i ] 
	                        , egraph.cons( elem_r[ i ] ) ) );

    elm_eq = canonize( substitute2( elm_eq, substs ) );

    axioms.push_back( egraph.mkImplies( egraph.cons( hyp
	                              , egraph.cons( elm_eq ) ) ) );

    cerr << "ADDING AXIOM: " << axioms.back( ) << endl;

    // Store new hyp ik != jk
    idx_hyp.pop_back( );
    idx_hyp.push_back( egraph.mkNot( egraph.cons( idx_eq ) ) );
  }

  return egraph.mkAnd( egraph.cons( axioms ) );
}
#endif

#endif

#ifdef PRODUCE_PROOF
Enode *
AXDiffPreproc::normalizeDiffs( Enode * formula )
{
  assert( formula );
  vector< Enode * > unprocessed_enodes;

  //
  // Detect diffs
  //
  egraph.initDupMap2( );
  egraph.initDup1( );

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
    if ( egraph.isDup1( enode ) )
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
      if ( !egraph.isDup1( arg ) )
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

    if ( enode->isEq( )
      && enode->get1st( )->getRetSort( ) == egraph.getSortIndex( ) )
    {
      Enode * l = enode->get1st( );
      Enode * r = enode->get2nd( );
      if ( l->isDiff( ) || r->isDiff( ) )
      {
	if ( l->isDiff( ) )
	{
	  if ( l->get1st( )->getIPartitions( ) == 6 
	    && l->get2nd( )->getIPartitions( ) == 6 
	    && r->getIPartitions( ) != 6 )
	  {
	    // Create a new ABcommon r
	    Enode * r_prime = freshVarFrom( l );
	    def_to_orig[ r_prime ] = l; 
	    egraph.storeDupMap2( r, r_prime ); 
	    index_variables.insert( r_prime );
	  }
	}
	if ( r->isDiff( ) )
	{
	  if ( r->get1st( )->getIPartitions( ) == 6 
	    && r->get2nd( )->getIPartitions( ) == 6 
	    && l->getIPartitions( ) != 6 )
	  {
	    // Create a new ABcommon l
	    Enode * l_prime = freshVarFrom( r );
	    def_to_orig[ l_prime ] = r; 
	    egraph.storeDupMap2( l, l_prime ); 
	    index_variables.insert( l_prime );
	  }
	}
      }
    }

    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  assert( formula );

  //
  // Replace diffs
  //

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

    Enode * result = egraph.copyEnodeEtypeTermWithCache( enode, true );

    egraph.storeDupMap2( enode, result );
  }

  Enode * new_formula = egraph.valDupMap2( formula );
  egraph.doneDupMap2( );

  assert( new_formula );

  return new_formula;
}

// Checks that all nodes are assigned to a partition
bool AXDiffPreproc::checkPartitions( Enode * formula )
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

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != egraph.enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      if ( !egraph.isDup1( arg ) )
	unprocessed_enodes.push_back( arg );
    }

    if ( enode->getIPartitions( ) == 0 )
    {
      egraph.doneDup1( );
      return false;
    }

    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  return true;
}
#endif
