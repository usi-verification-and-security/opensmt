/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

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

#include "TopLevelProp.h"
#include "LA.h"
#include "BVNormalize.h"

#define SIMPLIFY_TWIN_EQUALITIES 1

Enode *
TopLevelProp::doit( Enode * formula )
{
  assert( formula );
  //
  // We don't currently keep track of substitutions
  //
  // Learn some eq atoms useful for diamonds
  // benchmarks in SMTLIB
  //
#ifndef PRODUCE_PROOF
  if ( config.logic == QF_UF )
    formula = learnEqTransitivity( formula );
#endif
  //
  // Canonize Arithmetic
  //
  if ( config.logic == QF_IDL
    || config.logic == QF_RDL
    || config.logic == QF_LRA
    || config.logic == QF_LIA
    || config.logic == QF_UFIDL
    || config.logic == QF_UFLRA )
  {
    if ( ( config.logic == QF_UFIDL 
	|| config.logic == QF_UFLRA )
	&& config.sat_lazy_dtc != 0 )
      formula = egraph.canonizeDTC( formula );
    else
      formula = egraph.canonize( formula );
  }
  //
  // Canonize BVs
  //
  if ( config.logic == QF_BV )
  {
    BVNormalize normalizer( egraph, config );
    formula = normalizer.doit( formula );
  }

#ifndef PRODUCE_PROOF
  //
  // Repeat until fix point
  //
  bool stop = false;
  // If our target is to dump a formula to interpolate - skip fixpoint
  if ( config.sat_dump_rnd_inter != 0 ) stop = true;
  list< Enode * > conj;
  while ( !stop )
  {
    if ( formula->isTrue( ) 
      || formula->isFalse( ) )
    {
      stop = true;
      continue;
    }
    //
    // Step 1: gather top-level facts (including predicates)
    //
    map< Enode *, Enode * > substitutions;
    map< Enode *, Enode * > constant_substs;
    if ( !retrieveSubstitutions( formula, substitutions, constant_substs ) )
      return egraph.mkFalse( );
    //
    // Step 2: produce a new formula with substitutions done (if any to use)
    //
    bool sub_stop = true;

    // Normal substitutions
    if ( !substitutions.empty( ) )
      formula = substitute( formula, substitutions, sub_stop );

    /*
    // Constant substitutions
    if ( !constant_substs.empty( ) )
    {
      // Save constant substitutions
      for ( map< Enode *, Enode * >::iterator it = constant_substs.begin( )
	  ; it != constant_substs.end( )
	  ; it ++ )
      {
	map< Enode *, Enode * > tmp_map;
	tmp_map[ it->first ] = it->second;
	cerr << "Using: " << it->first << " --> " << it->second << endl;
	formula = substitute( formula, tmp_map, sub_stop );
	conj.push_back( egraph.mkEq( egraph.cons( it->first
		                   , egraph.cons( it->second ) ) ) );
	cerr << "It: " << formula << endl;
      }
    }
    */

    //
    // Step 3: Only for BV remove unconstrained terms
    //
    bool unc_stop = true;
    if ( config.logic == QF_BV
      || config.logic == QF_AX
      || config.logic == QF_AXDIFF )
    {
      formula = propagateUnconstrainedVariables( formula, unc_stop );
    }
    stop = sub_stop && unc_stop;
  }

  // Reinsert back constants substitutions
  conj.push_back( formula );
  formula = egraph.mkAnd( egraph.cons( conj ) );

#endif

  if ( config.logic == QF_IDL
    || config.logic == QF_RDL
    || config.logic == QF_LRA
    || config.logic == QF_LIA
    || config.logic == QF_UFIDL
    || config.logic == QF_UFLRA )
    formula = splitEqs( formula );

  return formula;
}

bool
TopLevelProp::retrieveSubstitutions( Enode * formula
                                   , map< Enode *, Enode * > & substitutions 
				   , map< Enode *, Enode * > & constant_substs )
{
  assert( substitutions.empty( ) );
  vector< Enode * > unprocessed_enodes;
  vector< bool >    unprocessed_polarity;
  vector< Enode * > top_level_arith;

  egraph.initDup1( );

  unprocessed_enodes  .push_back( formula );
  unprocessed_polarity.push_back( true );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    assert( unprocessed_enodes.size( ) == unprocessed_polarity.size( ) );
    Enode * enode = unprocessed_enodes.back( );
    const bool polarity = unprocessed_polarity.back( );
    unprocessed_enodes  .pop_back( );
    unprocessed_polarity.pop_back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
      continue;

    egraph.storeDup1( enode );
    //
    // Process children
    //
    if ( enode->isBooleanOperator( ) )
    {
      bool recurse = true;
      bool new_polarity;

      if ( enode->isAnd( ) && polarity )
	new_polarity = true;
      else if ( enode->isNot( ) )
	new_polarity = !polarity;
      else if ( enode->isOr( ) && !polarity )
	new_polarity = false;
      else
	recurse = false;

      if ( recurse )
      {
	Enode * arg_list;
	for ( arg_list = enode->getCdr( )
	    ; arg_list != egraph.enil
	    ; arg_list = arg_list->getCdr( ) )
	{
	  Enode * arg = arg_list->getCar( );
	  assert( arg->isTerm( ) );
	  unprocessed_enodes  .push_back( arg );
	  unprocessed_polarity.push_back( new_polarity );
	}
	continue;
      }
    }
    //
    // Add a new substitution for iff if possible
    //
    if ( enode->isIff( ) && polarity )
    {
      Enode * lhs = enode->get1st( );
      Enode * rhs = enode->get2nd( );

      if ( !lhs->isVar( ) && !rhs->isVar( ) )
	continue;

      Enode * var  = lhs->isVar( ) ? lhs : rhs;
      Enode * term = lhs->isVar( ) ? rhs : lhs;

      if ( contains( term, var ) )
	continue;

      // Substitute variable with term that does not contain it
      substitutions[ var ] = term;

#ifndef SMTCOMP
      // Save substitution for retrieving model
      egraph.addSubstitution( var, term );
#endif
    }
    //
    // Add a new substitution for some boolean or theory atom if possible
    //
    else if ( enode->isAtom( ) )
    {
      if ( enode->isTrue( ) )
      {
	substitutions[ enode ] = egraph.mkTrue( );
#ifndef SMTCOMP
	// Save substitution for retrieving model
	egraph.addSubstitution( enode, egraph.mkTrue( ) );
#endif
	continue;
      }

      if ( enode->isFalse( ) )
      {
	substitutions[ enode ] = egraph.mkFalse( );
#ifndef SMTCOMP
	// Save substitution for retrieving model
	egraph.addSubstitution( enode, egraph.mkFalse( ) );
#endif
	continue;
      }

      // Substitute boolean variable with true/false
      if ( enode->isVar( ) )
      {
	substitutions[ enode ] = polarity
	                                 ? egraph.mkTrue( )
	                                 : egraph.mkFalse( );
#ifndef SMTCOMP
	// Save substitution for retrieving model
	egraph.addSubstitution( enode, substitutions[ enode ] );
#endif
	continue;
      }

      if ( polarity )
	constant_substs[ enode ] = egraph.mkTrue( );
      else
	constant_substs[ enode ] = egraph.mkFalse( );

      assert( enode->isTAtom( ) );
      //
      // Substitute only positive equalities from now on
      //
      if ( !enode->isEq( ) || !polarity )
	continue;

      assert( enode->isEq( ) );
      assert( polarity );

      if ( config.logic == QF_UF 
	|| config.logic == QF_AX
	|| config.logic == QF_AXDIFF )
      {
	Enode * lhs = enode->get1st( );
	Enode * rhs = enode->get2nd( );

	if ( !lhs->isVar( ) && !rhs->isVar( ) )
	  continue;

	Enode * var  = lhs->isVar( ) ? lhs : rhs;
	Enode * term = lhs->isVar( ) ? rhs : lhs;

	if ( contains( term, var ) )
	  continue;

	// Substitute constants
	if ( term->isConstant( ) )
	{
	  constant_substs[ var ] = term;
	  continue;
	}

	// Substitute variable with term that does not contain it
	substitutions[ var ] = term;

#ifndef SMTCOMP
	// Save substitution for retrieving model
	egraph.addSubstitution( var, term );
#endif
      }
      else if ( config.logic == QF_IDL
	     || config.logic == QF_RDL
	     || config.logic == QF_LRA
	     || config.logic == QF_LIA
	     || config.logic == QF_UFIDL
	     || config.logic == QF_UFLRA )
      {
	top_level_arith.push_back( enode );
      }
      else if ( config.logic == QF_BV )
      {
	// TODO: do something for BV
      }
      /*
      else if ( config.logic == QF_AX 
	     || config.logic == QF_AXDIFF )
      {
	// TODO: do something more specific like gaussian elim
      }
      */
      // DO NOT REMOVE THIS COMMENT !!
      // IT IS USED BY CREATE_THEORY.SH SCRIPT !!
      // NEW_THEORY_INIT
      else
      {
	opensmt_error( "logic not supported yet" );
      }
    }
  }

  // Done with cache
  egraph.doneDup1( );
  bool res = true;
  //
  // Gaussian/Euler elimination for top-level arith
  //
  if ( config.logic == QF_IDL
    || config.logic == QF_RDL
    || config.logic == QF_LRA
  //|| config.logic == QF_LIA
  //|| config.logic == QF_UFIDL
    || config.logic == QF_UFLRA )
  {
    // Notice that arithmetic elimination may return unsat
    res = arithmeticElimination( top_level_arith, substitutions );
  }

  return res;
}

bool TopLevelProp::arithmeticElimination( vector< Enode * > & top_level_arith
                                        , map< Enode *, Enode * > & substitutions )
{
  vector< LAExpression * > equalities;
  // Initialize
  while ( !top_level_arith.empty( ) )
  {
    equalities.push_back( new LAExpression( top_level_arith.back( ) ) );
    top_level_arith.pop_back( );
  }
  //
  // If just one equality, produce substitution right away
  //
  if ( equalities.size( ) == 0 )
    ; // Do nothing
  else if ( equalities.size( ) == 1 )
  {
    LAExpression & lae = *equalities[ 0 ];
    if ( lae.solve( ) == NULL )
      opensmt_error( "there is something wrong here" );
    pair< Enode *, Enode * > sub = lae.getSubst( egraph );
    assert( sub.first );
    assert( sub.second );
    assert( substitutions.find( sub.first ) == substitutions.end( ) );
    substitutions[ sub.first ] = sub.second;
#ifndef SMTCOMP
    // Save substitution for retrieving model
    egraph.addSubstitution( sub.first, sub.second );
#endif
  }
  //
  // Otherwise obtain substitutions
  // by means of Gaussian/Euler Elimination
  //
  else
  {
    //
    // FORWARD substitution
    // We put the matrix equalities into upper triangular form
    //
    for ( unsigned i = 0 ; i + 1 < equalities.size( ) ; i ++ )
    {
      LAExpression & s = *equalities[ i ];
      // Solve w.r.t. first variable
      if ( s.solve( ) == NULL )
      {
	if ( s.toEnode( egraph ) == egraph.mkTrue( ) )
	  continue;
	assert( s.toEnode( egraph ) == egraph.mkFalse( ) );
	return false;
      }
      // Use the first variable x in s to generate a
      // substitution and replace x in lac
      for ( unsigned j = i + 1 ; j < equalities.size( ) ; j ++ )
      {
	LAExpression & lac = *equalities[ j ];
	combine( s, lac );
      }
    }
    //
    // BACKWARD substitution
    // From the last equality to the first we put
    // the matrix equalities into canonical form
    //
    for ( int i = equalities.size( ) - 1 ; i >= 1 ; i -- )
    {
      LAExpression & s = *equalities[ i ];
      // Solve w.r.t. first variable
      if ( s.solve( ) == NULL )
      {
	if ( s.toEnode( egraph ) == egraph.mkTrue( ) )
	  continue;
	assert( s.toEnode( egraph ) == egraph.mkFalse( ) );
	return false;
      }
      // Use the first variable x in s as a
      // substitution and replace x in lac
      for ( int j = i - 1 ; j >= 0 ; j -- )
      {
	LAExpression & lac = *equalities[ j ];
	combine( s, lac );
      }
    }
    //
    // Now, for each row we get a substitution
    //
    for ( unsigned i = 0 ; i < equalities.size( ) ; i ++ )
    {
      LAExpression & lae = *equalities[ i ];
      pair< Enode *, Enode * > sub = lae.getSubst( egraph );
      if ( sub.first == NULL ) continue;
      assert( sub.second );
      assert( substitutions.find( sub.first ) == substitutions.end( ) );
      substitutions[ sub.first ] = sub.second;

#ifndef SMTCOMP
      // Save substitution for retrieving model
      egraph.addSubstitution( sub.first, sub.second );
#endif
    }
  }
  // Clean constraints
  while ( !equalities.empty( ) )
  {
    delete equalities.back( );
    equalities.pop_back( );
  }

  return true;
}

bool
TopLevelProp::contains( Enode * term, Enode * var )
{
  vector< Enode * > unprocessed_enodes;
  egraph.initDup2( );

  unprocessed_enodes.push_back( term );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    if ( enode == var )
    {
      egraph.doneDup2( );
      return true;
    }
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
    for ( arg_list = enode->getCdr( ) ;
	arg_list != egraph.enil ;
	arg_list = arg_list->getCdr( ) )
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
    egraph.storeDup2( enode );
  }

  egraph.doneDup2( );

  return false;
}

Enode *
TopLevelProp::substitute( Enode * formula
                        , map< Enode *, Enode * > & substitutions
                        , bool & sub_stop )
{
  assert( formula );
  list< Enode * > reinsert_back;

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

    map< Enode *, Enode * >::iterator it = substitutions.find( enode );
    if ( enode->isVar( ) )
    {
      // Substitute
      if ( it != substitutions.end( ) )
	result = it->second;
    }
    else if ( enode->isTAtom( ) )
    {
      // Substitute
      if ( it != substitutions.end( ) )
	result = it->second;
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    else
      sub_stop = false;

    //
    // Canonize again arithmetic/bitvectors theory atoms
    //
    if ( result->isTAtom( ) && !result->isUp( ) )
    {
      if ( config.logic == QF_IDL
	|| config.logic == QF_RDL
	|| config.logic == QF_LRA
	|| config.logic == QF_LIA
	|| config.logic == QF_UFIDL
	|| config.logic == QF_UFLRA )
      {
	LAExpression a( result );
	result = a.toEnode( egraph );
      }
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );

  egraph.doneDupMap1( );
  assert( new_formula );
  return new_formula;
}

Enode *
TopLevelProp::learnEqTransitivity( Enode * formula )
{
  list< Enode * > implications;
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
    for ( arg_list = enode->getCdr( ) ;
	arg_list != egraph.enil ;
	arg_list = arg_list->getCdr( ) )
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
    //
    // Add (or (and (= x w) (= w z)) (and (= x y) (= y z))) -> (= x z)
    //
    const bool condition1 = enode->isOr( ) && enode->getArity( ) == 2
      && enode->get1st( )->isAnd( ) && enode->get1st( )->get1st( )->isEq( ) && enode->get1st( )->get2nd( )->isEq( )
      && enode->get2nd( )->isAnd( ) && enode->get2nd( )->get1st( )->isEq( ) && enode->get2nd( )->get2nd( )->isEq( );

    if ( condition1 )
    {
      //
      // (= v1 v2) (= v3 v4)
      //
      Enode * v1 = enode->get1st( )->get1st( )->get1st( );
      Enode * v2 = enode->get1st( )->get1st( )->get2nd( );
      Enode * v3 = enode->get1st( )->get2nd( )->get1st( );
      Enode * v4 = enode->get1st( )->get2nd( )->get2nd( );
      //
      // (= t1 t2) (= t3 t4)
      //
      Enode * t1 = enode->get2nd( )->get1st( )->get1st( );
      Enode * t2 = enode->get2nd( )->get1st( )->get2nd( );
      Enode * t3 = enode->get2nd( )->get2nd( )->get1st( );
      Enode * t4 = enode->get2nd( )->get2nd( )->get2nd( );
      //
      // Detect bridging variables
      //
      const bool condition2a = v1 == v3 || v1 == v4 || v2 == v3 || v2 == v4;
      const bool condition2b = t1 == t3 || t1 == t4 || t2 == t3 || t2 == t4;

      if ( condition2a && condition2b )
      {
	Enode * w  = (v1 == v3 || v1 == v4 ? v1 : v2);
	Enode * x1 = (v1 == w ? v2 : v1);
	Enode * z1 = (v3 == w ? v4 : v3);

	Enode * y  = (t1 == t3 || t1 == t4 ? t1 : t2);
	Enode * x2 = (t1 == y ? t2 : t1);
	Enode * z2 = (t3 == y ? t4 : t3);

	const bool condition2 = (x1 == x2 && z1 == z2)
	  || (x1 == z2 && x2 == z1);

	if ( condition2 )
	{
	  Enode * impl = egraph.mkEq( egraph.cons( x1, egraph.cons( z1 ) ) );
	  implications.push_back( egraph.mkImplies( egraph.cons( enode, egraph.cons( impl ) ) ) );
	}
      }
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( result != NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * result = egraph.valDupMap1( formula );
  egraph.doneDupMap1( );

  if ( !implications.empty( ) )
  {
    implications.push_back( result );
    result = egraph.mkAnd( egraph.cons( implications ) );
  }

  return result;
}

//
// Repeat until fix point:
// . Compute variables that occur only once (unconstrained variables)
// . Replace unconstrained terms (those that contain an unconstrained variable) with a free variable
//
Enode *
TopLevelProp::propagateUnconstrainedVariables( Enode * formula, bool & unc_stop )
{
  bool fix_point_not_reached = true;
  while ( fix_point_not_reached )
  {
    vector< int > id_to_inc_edges;
    computeIncomingEdges( formula, id_to_inc_edges );
    fix_point_not_reached = false;
    formula = replaceUnconstrainedTerms( formula, id_to_inc_edges, fix_point_not_reached );
    // unc_stop is true if at least another iteration is done, which
    // means that something has been simplified
    if ( unc_stop && fix_point_not_reached ) unc_stop = false;
  }

  return formula;
}

Enode *
TopLevelProp::replaceUnconstrainedTerms( Enode * formula
    , vector< int > & //id_to_inc_edges
    , bool & //fix_point_not_reached 
    )
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
    //
    // Operators for which ONE unconstrained variable is enough
    //
    if ( false ) { }
    else if ( enode->isEq ( )
	   || enode->isNot( )
	   || enode->isXor( )
	   )
    {
      for ( Enode * ll = enode->getCdr( )
	  ; !ll->isEnil( )
	  ; ll = ll->getCdr( ) )
      {
	Enode * arg = egraph.valDupMap1( ll->getCar( ) );
	if ( arg->isVar( )
	    && id_to_inc_edges[ arg->getId( ) ] == 1 )
	{
	  // Allocate a new unconstrained variable for the term
	  char def_name[ 32 ];
	  sprintf( def_name, "UNC_%d", enode->getId( ) );
	  egraph.newSymbol( def_name, DTYPE_BOOL );
	  result = egraph.mkVar( def_name );
	  if ( static_cast< int >( id_to_inc_edges.size( ) ) < result->getId( ) )
	    id_to_inc_edges.resize( result->getId( ) + 1, 0 );
	  fix_point_not_reached = true;
	  break;
	}
      }
    }
    else if ( enode->isAnd( )
	|| enode->isOr ( ) )
    {
      bool unconstrained = true;
      for ( Enode * ll = enode->getCdr( )
	  ; !ll->isEnil( ) && unconstrained
	  ; ll = ll->getCdr( ) )
      {
	Enode * arg = egraph.valDupMap1( ll->getCar( ) );
	if ( !arg->isVar( )
	    || id_to_inc_edges[ arg->getId( ) ] != 1 )
	  unconstrained = false;
      }
      if ( unconstrained )
      {
	// Allocate a new unconstrained variable for the term
	char def_name[ 32 ];
	sprintf( def_name, "UNC_%d", enode->getId( ) );
	egraph.newSymbol( def_name, DTYPE_BOOL );
	result = egraph.mkVar( def_name );
	if ( static_cast< int >( id_to_inc_edges.size( ) ) < result->getId( ) )
	  id_to_inc_edges.resize( result->getId( ) + 1, 0 );
	fix_point_not_reached = true;
      }
    }
    else if ( enode->isIte( ) )
    {
      Enode * i = enode->get1st( );
      Enode * t = enode->get2nd( );
      Enode * e = enode->get3rd( );

      if ( i->isVar( ) && id_to_inc_edges[ i->getId( ) ] == 1 )
      {
	if ( (t->isVar( ) && id_to_inc_edges[ t->getId( ) ] == 1)
	    || (e->isVar( ) && id_to_inc_edges[ e->getId( ) ] == 1) )
	{
	  char def_name[ 32 ];
	  sprintf( def_name, "UNC_%d", enode->getId( ) );
	  egraph.newSymbol( def_name, DTYPE_BITVEC | enode->getWidth( ) );
	  result = egraph.mkVar( def_name );
	  if ( static_cast< int >( id_to_inc_edges.size( ) ) < result->getId( ) )
	    id_to_inc_edges.resize( result->getId( ) + 1, 0 );
	  fix_point_not_reached = true;
	}
      }
    }
    //
    // If nothing has been done copy and simplify
    //
    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
#ifdef PRODUCE_PROOF
    egraph.setIPartitions(result, egraph.getIPartitions(enode));
#endif
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );
  egraph.doneDupMap1( );

  return new_formula;
  */
  return formula;
}

void TopLevelProp::computeIncomingEdges( Enode * formula
				       , vector< int > & id_to_inc_edges )
{
  assert( formula );

  vector< Enode * > unprocessed_enodes;
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
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    for ( Enode * ll = enode->getCdr( )
	; !ll->isEnil( )
	; ll = ll->getCdr( ) )
    {
      Enode * arg = ll->getCar( );
      if ( arg->getId( ) >= (enodeid_t)id_to_inc_edges.size( ) )
	id_to_inc_edges.resize( arg->getId( ) + 1, 0 );
      id_to_inc_edges[ arg->getId( ) ] ++;
    }

    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );
}

Enode *
TopLevelProp::splitEqs( Enode * formula )
{
  assert( config.logic == QF_IDL
       || config.logic == QF_RDL
       || config.logic == QF_LRA
       || config.logic == QF_LIA
       || config.logic == QF_UFIDL
       || config.logic == QF_UFLRA );

  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

  list< Enode * > dtc_axioms;

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
    //
    // Replace arithmetic atoms with canonized version
    //
    if ( enode->isTAtom( ) 
      && enode->isEq( ) )
    {
      // 
      // If DTC is active
      //
      if ( ( config.logic == QF_UFIDL
	  || config.logic == QF_UFLRA )
	  && config.sat_lazy_dtc != 0 )
      {
	//
	// These equalities will be given to the arithmetic 
	// solvers, and hence split, only if they are not 
	// "purely" uf (at the root level -- we assume we 
	// did purification before).
	//
	if ( !egraph.isRootUF( enode ) )
	{
	  LAExpression a( enode );
	  Enode * e = a.toEnode( egraph );
	  Enode * lhs = e->get1st( );
	  Enode * rhs = e->get2nd( );
	  Enode * leq = egraph.mkLeq( egraph.cons( lhs
		                    , egraph.cons( rhs ) ) );
	  LAExpression b( leq );
	  leq = b.toEnode( egraph );
	  Enode * geq = egraph.mkGeq( egraph.cons( lhs
		                    , egraph.cons( rhs ) ) );
	  LAExpression c( geq );
	  geq = c.toEnode( egraph );
	  Enode * not_e = egraph.mkNot( egraph.cons( enode ) );
	  Enode * not_l = egraph.mkNot( egraph.cons( leq ) );
	  Enode * not_g = egraph.mkNot( egraph.cons( geq ) );
	  // Add clause ( !x=y v x<=y )
	  Enode * c1 = egraph.mkOr( egraph.cons( not_e
		                  , egraph.cons( leq ) ) );
	  // Add clause ( !x=y v x>=y )
	  Enode * c2 = egraph.mkOr( egraph.cons( not_e
		                  , egraph.cons( geq ) ) );
	  // Add clause ( x=y v !x>=y v !x<=y )
	  Enode * c3 = egraph.mkOr( egraph.cons( enode
		                  , egraph.cons( not_l
		                  , egraph.cons( not_g ) ) ) );
	  // Add conjunction of clauses
	  Enode * ax = egraph.mkAnd( egraph.cons( c1
	 	                   , egraph.cons( c2
		                   , egraph.cons( c3 ) ) ) );

	  dtc_axioms.push_back( ax );
	}
	result = enode;
      }
      else
      {
	LAExpression a( enode );
	Enode * e = a.toEnode( egraph );
	Enode * lhs = e->get1st( );
	Enode * rhs = e->get2nd( );
	Enode * leq = egraph.mkLeq( egraph.cons( lhs, egraph.cons( rhs ) ) );
	LAExpression b( leq );
	leq = b.toEnode( egraph );
	Enode * geq = egraph.mkGeq( egraph.cons( lhs, egraph.cons( rhs ) ) );
	LAExpression c( geq );
	geq = c.toEnode( egraph );
	result = egraph.mkAnd( egraph.cons( leq, egraph.cons( geq ) ) );
      }
    }
    //
    // If nothing have been done copy and simplify
    //
    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );
  egraph.doneDupMap1( );

  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
      && config.sat_lazy_dtc != 0 )
  {
    dtc_axioms.push_back( new_formula );
    new_formula = egraph.mkAnd( egraph.cons( dtc_axioms ) );
  }

  return new_formula;
}
