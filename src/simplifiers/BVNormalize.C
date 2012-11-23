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

#include "BVNormalize.h"

Enode *
BVNormalize::doit( Enode * formula )
{
  /*
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
    if ( enode->isBooleanOperator( ) )
    {
      Enode * arg_list;
      for ( arg_list = enode->getCdr( ) 
	  ; arg_list != egraph.enil 
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	//
	// Push only if it is unprocessed
	// boolean operator
	//
	if ( egraph.valDupMap1( arg ) == NULL )
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
    Enode * result = NULL;

    if ( enode->isTAtom( ) )
      result = normalize( enode );
    //
    // If nothing has been done copy and simplify
    //
    if ( result == NULL )
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }

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

Enode *
BVNormalize::normalize( Enode * term )
{
  /*
  assert( term );
  //
  // Simplification for predicates
  //
  assert( term->isDistinct( ) 
       || term->isEq      ( ) 
       || term->isBvule   ( ) 
       || term->isBvsle   ( ) );
  assert( term->getArity( ) == 2 );

  if ( term->isBvule   ( ) 
    || term->isBvsle   ( )
    || term->isDistinct( ) ) return term;

  Enode * lhs = term->get1st( ); 
  Enode * rhs = term->get2nd( ); 
  //
  // Handle some particular case
  //
  if ( term->isEq( ) )
  {
    int lhs_se, rhs_se;
    if ( lhs->isBvmul( ) 
      && rhs->isBvmul( ) 
      && lhs->get1st( ) == rhs->get1st( ) )
    {
      lhs = lhs->get2nd( );
      rhs = rhs->get2nd( );
    }
    else if ( lhs->isSignExtend( &lhs_se ) 
	   && rhs->isSignExtend( &rhs_se ) 
	   && lhs_se == rhs_se )
    {
      lhs = lhs->get1st( );
      rhs = rhs->get1st( );
    }
  }
  // 
  // Map between node and coefficient
  //
  map< enodeid_t, mpz_class * > term_to_coeff;
  map< enodeid_t, Enode * > id_to_enode;
  vector< mpz_class * > garbage;
  //
  // For now process just equalities and signed le, which
  // can be safely rewritten as usual (I think ...)
  //
  mpz_class const_value( 0 );
  scanPolynome( lhs, term_to_coeff, const_value, id_to_enode, garbage, false );
  scanPolynome( rhs, term_to_coeff, const_value, id_to_enode, garbage, true ); 

  mpz_class one  (  1 );
  mpz_class minus( -1 );
  mpz_class zero (  0 );

  //
  // Build new lhs and rhs
  //
  Enode * new_lhs = const_cast< Enode * >( egraph.enil );
  Enode * new_rhs = const_cast< Enode * >( egraph.enil );
  for ( map< enodeid_t, mpz_class * >::iterator it = term_to_coeff.begin( ) 
      ; it != term_to_coeff.end( ) 
      ; it ++ )
  {
    Enode * e = id_to_enode[ it->first ];

    if ( *(it->second) == one )
    {
      new_lhs = new_lhs->isEnil( ) ? e : egraph.mkBvadd( egraph.cons( e, egraph.cons( new_lhs ) ) );
    }
    else if ( *(it->second) == minus )
    {
      new_rhs = new_rhs->isEnil( ) ? e : egraph.mkBvadd( egraph.cons( e, egraph.cons( new_rhs ) ) );
    }
    else if ( *(it->second) > zero )
    {
      Enode * num = makeNumberFromGmp( *(it->second ), e->getWidth( ) );
      Enode * mon = egraph.mkBvmul( egraph.cons( num, egraph.cons( e ) ) );
      new_lhs = new_lhs->isEnil( ) ? mon : egraph.mkBvadd( egraph.cons( mon, egraph.cons( new_lhs ) ) );
    }
    else if ( *(it->second) < zero )
    {
      mpz_class abs = *(it->second) * -1;
      Enode * num = makeNumberFromGmp( abs, e->getWidth( ) );
      Enode * mon = egraph.mkBvmul( egraph.cons( num, egraph.cons( e ) ) );
      new_rhs = new_rhs->isEnil( ) ? mon : egraph.mkBvadd( egraph.cons( mon, egraph.cons( new_rhs ) ) );
    }
  } 

  if ( new_lhs->isEnil( ) && new_rhs->isEnil( ) )
  {
    if ( term->isEq( ) )
    {
      if ( const_value == 0 )
	return egraph.mkTrue ( );
      else
	return egraph.mkFalse( );
    }
    else
    {
      error( "Unsupported operator: ", term->getCar( ) );
    }
  }

  assert( !new_lhs->isEnil( ) 
       || !new_rhs->isEnil( ) );
  const int width = new_lhs->isEnil   ( ) 
                  ? new_rhs->getWidth ( ) 
		  : new_lhs->getWidth ( );
  //
  // Add constant
  //
  if ( const_value > zero )
  {
    Enode * mon = makeNumberFromGmp( const_value, width );
    new_lhs = new_lhs->isEnil( ) 
	    ? mon 
	    : egraph.mkBvadd( egraph.cons( mon, egraph.cons( new_lhs ) ) );
  }
  if ( const_value < zero )
  {
    mpz_class abs = const_value * -1;
    Enode * mon = makeNumberFromGmp( abs, width );
    new_rhs = new_rhs->isEnil( ) 
	    ? mon 
	    : egraph.mkBvadd( egraph.cons( mon, egraph.cons( new_rhs ) ) );
  }
  //
  // Put zero if a side is empty
  //
  if ( new_lhs->isEnil( ) ) new_lhs = makeNumberFromGmp( zero, lhs->getWidth( ) );
  if ( new_rhs->isEnil( ) ) new_rhs = makeNumberFromGmp( zero, rhs->getWidth( ) );

  Enode * res = NULL;
  //
  // Return the right predicate
  //
       if ( term->isEq   ( ) ) res = egraph.mkEq   ( egraph.cons( new_lhs, egraph.cons( new_rhs ) ) );
  // else if ( term->isBvsle( ) ) res = egraph.mkBvsle( egraph.cons( new_lhs, egraph.cons( new_rhs ) ) );

  assert( res );
  //
  // Clean created numbers
  //
  while( !garbage.empty( ) ) 
  {
    mpz_class * e = garbage.back( );
    garbage.pop_back( );
    delete e;
  }

  return res;
  */
  return term;
}

Enode *
BVNormalize::makeNumberFromGmp( mpz_class & //n
                              , const int //width 
			      )
{
  /*
  assert( n >= 0 );
  string s = n.get_str( 2 );
  string new_bin_value;
  //
  // Handle overflow 
  //
  if ( (int)s.size( ) > width )
  {
    s = s.substr( s.size( ) - width, width );
    assert( (int)s.size( ) == width );
  }
  assert( width >= (int)s.size( ) );
  if( width - (int)s.size( ) > 0 )
    new_bin_value.insert( 0, width - s.size( ), '0' );
  new_bin_value += s;
  return egraph.mkBvnum( const_cast< char * >(new_bin_value.c_str( )) );
  */
  return NULL;
}

void
BVNormalize::scanPolynome( Enode *                         //p
                         , map< enodeid_t, mpz_class * > & //term_to_coeff
			 , mpz_class &                     //const_value
			 , map< enodeid_t, Enode * > &     //id_to_enode
			 , vector< mpz_class * > &         //garbage
			 , bool                            //negate 
			 )
{
  /*
  vector< Enode * >     unprocessed_enodes;
  vector< mpz_class * > unprocessed_coeffs;

  unprocessed_enodes.push_back( p );
  unprocessed_coeffs.push_back( negate 
                              ? new mpz_class( -1 ) 
			      : new mpz_class( 1 ) );
  garbage.push_back( unprocessed_coeffs.back( ) );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    assert( unprocessed_enodes.size( ) == unprocessed_coeffs.size( ) );
    Enode * enode = unprocessed_enodes.back( );
    mpz_class * coeff = unprocessed_coeffs.back( );
    unprocessed_enodes.pop_back( );
    unprocessed_coeffs.pop_back( );

    //
    // Process children
    //
    if ( enode->isBvadd( ) )
    {
      assert( enode->getArity( ) == 2 );
      Enode * a = enode->get1st( );
      Enode * b = enode->get2nd( );
      unprocessed_enodes.push_back( a );
      unprocessed_coeffs.push_back( coeff );
      unprocessed_enodes.push_back( b );
      unprocessed_coeffs.push_back( coeff );
    }
    else if ( enode->isBvsub( ) )
    {
      assert( enode->getArity( ) == 2 );
      Enode * a = enode->get1st( );
      Enode * b = enode->get2nd( );
      unprocessed_enodes.push_back( a );
      unprocessed_coeffs.push_back( coeff );
      unprocessed_enodes.push_back( b );
      mpz_class * neg_coeff = new mpz_class;
      garbage.push_back( neg_coeff );
      (*neg_coeff) = (*coeff) * -1;
      unprocessed_coeffs.push_back( neg_coeff );
    }
    else if ( enode->isBvneg( ) )
    {
      assert( enode->getArity( ) == 1 );
      Enode * a = enode->get1st( );
      unprocessed_enodes.push_back( a );
      mpz_class * neg_coeff = new mpz_class;
      garbage.push_back( neg_coeff );
      (*neg_coeff) = (*coeff) * -1;
      unprocessed_coeffs.push_back( neg_coeff );
    }
    else if ( enode->isBvmul( ) 
	   && ( enode->get1st( )->isConstant( )  
	     || enode->get2nd( )->isConstant( ) ) )
    {
      Enode * c = enode->get1st( )->isConstant( ) ? enode->get1st( ) : enode->get2nd( );
      Enode * t = enode->get1st( )->isConstant( ) ? enode->get2nd( ) : enode->get1st( );
      mpz_class cval( c->getCar( )->getName( ), 2 );
      unprocessed_enodes.push_back( t );
      mpz_class * new_coeff = new mpz_class;
      garbage.push_back( new_coeff );
      (*new_coeff) = (*coeff) * cval;
      unprocessed_coeffs.push_back( new_coeff );
    }
    //
    // If constant, add to the value for constant
    //
    else if ( enode->isConstant( ) )
    {
      mpz_class cval( enode->getCar( )->getName( ), 2 );
      const_value += (*coeff) * cval;
    }
    //
    // Otherwise add an entry for this term
    //
    else
    {
      id_to_enode[ enode->getId( ) ] = enode;
      map< enodeid_t, mpz_class * >::iterator it = term_to_coeff.find( enode->getId( ) );
      //
      // Create new entry
      //
      if ( it == term_to_coeff.end( ) )
      {
	term_to_coeff[ enode->getId( ) ] = coeff;	
      }
      //
      // Otherwise sum to the existing one
      //
      else
      {
	mpz_class * new_coeff = new mpz_class;
	garbage.push_back( new_coeff );
	(*new_coeff) = (*(it->second)) + (*coeff);
	term_to_coeff[ enode->getId( ) ] = new_coeff;
      }
    }
  }
*/
}
