/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Aliaksei Tsitovich <aliaksei.tsitovich@gmail.com>

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

#include "LA.h"

//
// Scan the enode and prepare the polynome
// Notice that it won't work on non-linear
// polynomes -- "unpredictable" result
//
void LAExpression::initialize( Enode * e )
{
  assert( e->isEq( ) || e->isLeq( ) );
  integers = false;

  vector< Enode * > curr_term;
  vector< Real >    curr_const;

  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );
  curr_term .push_back( lhs );
  curr_const.push_back( 1 );
  curr_term .push_back( rhs );
  curr_const.push_back( -1 );

  while ( !curr_term.empty( ) )
  {
    Enode * t = curr_term.back( );
    curr_term.pop_back( );
    Real c = curr_const.back( );
    curr_const.pop_back( );
    //
    // Only 3 cases are allowed
    //
    // If it is plus, enqueue the arguments with same constant
    //
    if ( t->isPlus( ) )
    {
      for ( Enode * arg_list = t->getCdr( )
	  ; !arg_list->isEnil( )
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	curr_term .push_back( arg );
	curr_const.push_back( c );
      }
    }
    //
    // If it is times, then one side must be constant, other
    // is enqueued with a new constant
    //
    else if ( t->isTimes( ) )
    {
      assert( t->getArity( ) == 2 );
      Enode * x = t->get1st( );
      Enode * y = t->get2nd( );
      assert( x->isConstant( ) || y->isConstant( ) );
      if ( y->isConstant( ) )
      {
	Enode * tmp = y;
	y = x;
	x = tmp;
      }

      Real new_c = x->getValue( );
      new_c = new_c * c;
      curr_term .push_back( y );
      curr_const.push_back( new_c );
    }
    //
    // Otherwise it is a variable or UF or constant
    //
    else
    {
      assert( t->isVar( ) || t->isConstant( ) || t->isUf( ) );
      if ( t->isConstant( ) )
      {
	const Real & tval = t->getValue( );
	polynome[ 0 ] += tval * c;
      }
      else
      {
	if ( t->hasSortInt( ) )
	  integers = true;

	polynome_t::iterator it = polynome.find( t );
	if ( it != polynome.end( ) )
	{
	  it->second += c;
	  if ( it->first != 0 && it->second == 0 )
	    polynome.erase( it );
	}
	else
	  polynome[ t ] = c;
      }
    }
  }

  if ( polynome.find( 0 ) == polynome.end( ) )
    polynome[ 0 ] = 0;
  //
  // Canonize
  //
  canonize( );
}

Enode * LAExpression::toEnode( Egraph & egraph )
{
  assert( polynome.find( 0 ) != polynome.end( ) );
  assert( polynome.size( ) > 0 );
  //
  // There is at least one variable
  //
  list< Enode * > sum_list;
  Real constant = 0;
  for ( polynome_t::iterator it = polynome.begin( )
      ; it != polynome.end( )
      ; it ++ )
  {
    if ( it->first == 0 )
      constant = it->second;
    else
    {
      Enode * coeff = egraph.mkNum( it->second );
      Enode * vv = it->first;
      sum_list.push_back( egraph.mkTimes( egraph.cons( coeff, egraph.cons( vv ) ) ) );
    }
  }
  if ( sum_list.empty( ) )
  {
    Real zero = 0;
    sum_list.push_back( egraph.mkNum( zero ) );
  }
  //
  // Return in the form ax + by + ... = -c
  //
  if ( r == EQ || r == LEQ )
  {
    Enode * poly = egraph.mkPlus( egraph.cons( sum_list ) );
    constant = -constant;
    Enode * c = egraph.mkNum( constant );
    if ( r == EQ )
      return egraph.mkEq( egraph.cons( poly, egraph.cons( c ) ) );
    else
      return egraph.mkLeq( egraph.cons( poly, egraph.cons( c ) ) );
  }
  //
  // Return in the form ax + by + ... + c
  //
  assert( r == UNDEF );
  sum_list.push_back( egraph.mkNum( constant ) );
  Enode * poly = egraph.mkPlus( egraph.cons( sum_list ) );

  return poly;
}
//
// Print
//
void LAExpression::print( ostream & os )
{
  assert( polynome.find( 0 ) != polynome.end( ) );
  assert( polynome.size( ) > 0 );
  if ( r == EQ )
    os << "(=";
  else if ( r == LEQ )
    os << "(<=";
  Real constant = 0;
  if ( polynome.size( ) == 1 )
    os << " " << polynome[ 0 ];
  else
  {
    //
    // There is at least one variable
    //
    os << " (+";
    list< Enode * > sum_list;
    for ( polynome_t::iterator it = polynome.begin( )
	; it != polynome.end( )
	; it ++ )
    {
      if ( it->first == 0 )
	constant = -it->second;
      else
	os << " (* " << it->second << " " << it->first << ")";
    }
    os << ")";
  }
  if ( r == EQ || r == LEQ )
    os << " " << constant << ")";
}
//
// Produce a substitution
//
pair< Enode *, Enode * > LAExpression::getSubst( Egraph & egraph )
{
  assert( polynome.find( 0 ) != polynome.end( ) );
  assert( r != UNDEF );

  if ( integers )
    return getSubstInt( egraph );
  else
    return getSubstReal( egraph );
}

pair< Enode *, Enode * > LAExpression::getSubstInt( Egraph & egraph )
{
  // See if cheap substitution, not requiring our friend
  // Euler, can be done
  bool all_ones = true;
  for ( polynome_t::iterator it = polynome.begin( )
      ; it != polynome.end( ) && all_ones
      ; it ++ )
  {
     all_ones = it->first  == 0 
             || it->second == 1
             || it->second == -1;
  }

  if ( all_ones )
    return getSubstReal( egraph );

  opensmt_error( "IMPLEMENT EULER" );
  Enode * v1, * v2;
  return make_pair( v1, v2 );
}

pair< Enode *, Enode * > LAExpression::getSubstReal( Egraph & egraph )
{
  if ( polynome.size( ) == 1 )
  {
    assert( polynome.find( 0 ) != polynome.end( ) );
    Enode * v1 = NULL, * v2 = NULL;
    return make_pair( v1, v2 );
  }
  //
  // There is at least one variable
  //
  //
  // Solve w.r.t. first variable
  //
  solve( );
  list< Enode * > sum_list;
  Real constant = 0;
  Enode * var = NULL;
  for ( polynome_t::iterator it = polynome.begin( )
      ; it != polynome.end( )
      ; it ++ )
  {
    if ( it->first == 0 )
      constant = -it->second;
    else
    {
      if ( var == NULL )
      {
	var = it->first;
	assert( it->second == 1 );
      }
      else
      {
	Real coeff = -it->second;
	Enode * c = egraph.mkNum( coeff );
	Enode * vv = it->first;
	sum_list.push_back( egraph.mkTimes( egraph.cons( c
		                          , egraph.cons( vv ) ) ) );
      }
    }
  }
  sum_list.push_back( egraph.mkNum( constant ) );
  Enode * poly = egraph.mkPlus( egraph.cons( sum_list ) );

  return make_pair( var, poly );
}
//
// Solve w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
Enode *
LAExpression::solve( )
{
  assert(  r == EQ );
  assert( polynome.find( 0 ) != polynome.end( ) );
  if ( polynome.size( ) == 1 )
  {
    assert( polynome.find( 0 ) != polynome.end( ) );
    return NULL;
  }
  //
  // Get first useful variable
  //
  polynome_t::iterator it = polynome.begin( );
  if ( it->first == 0 ) it ++;
  Enode * var = it->first;
  const Real coeff = it->second;
  //
  // Divide polynome by coeff
  //
  for ( it = polynome.begin( )
      ; it != polynome.end( )
      ; it ++ )
  {
    it->second /= coeff;
  }
  assert( polynome[ var ] == 1 );
  //
  // Return substitution
  //
  return var;
}
//
// Canonize w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
void
LAExpression::canonize( )
{
  assert( polynome.find( 0 ) != polynome.end( ) );

  if ( integers )
    canonizeInt( );
  else
    canonizeReal( );
}

//
// We assume (and check) that denominators
// of coefficients are 1
//
void
LAExpression::canonizeInt( )
{
  assert( checkIntCoefficients( ) );

  if ( polynome.size( ) == 1 )
  {
    assert( polynome.find( 0 ) != polynome.end( ) );
    return;
  }

  // Iterate through the polynome and
  // collect the GCD
  polynome_t::iterator it = polynome.begin( );
  Integer igcd = 0;
  for ( ; it != polynome.end( ) ; ++ it )
  {
    // Skip constant (if there)
    if ( it->first == 0 ) continue;
    Integer coeff = (it->second).get_num( );
    if ( igcd == 0 )
    {
      igcd = coeff;
      continue;
    }
    gcd( igcd, igcd, coeff );
  }

  // Nothing to do
  if ( igcd == 1 )
    return;
  const Real abs_igcd = ( igcd > 0 ? igcd : -igcd );
  const Real rgcd = Real( abs_igcd ); 

  // Divide each term by gcd
  for ( it = polynome.begin( ) 
      ; it != polynome.end( ) 
      ; ++ it )
  {
    it->second /= rgcd;
  }
  // Nothing to do
  if ( polynome.find( 0 ) == polynome.end( ) )
    return;
  // Check if equality is unsat
  if ( (polynome[ 0 ]).get_den( ) != 1 )
  {
    // Write a false polynome
    if ( r == EQ )
    {
      polynome.clear( );
      polynome[ 0 ] = 1;
    }
    // Tighten
    if ( r == LEQ )
      polynome[ 0 ] = Real( polynome[ 0 ].ceil( ) );
  }
  assert( checkIntCoefficients( ) );  
}

bool
LAExpression::checkIntCoefficients( )
{
  polynome_t::iterator it;
  for ( it = polynome.begin( ) 
      ; it != polynome.end( ) 
      ; ++ it )
  {
    const Real coeff = it->second;
    if ( coeff.get_den( ) != 1 )
      return false;
  }

  return true;
}

void
LAExpression::canonizeReal( )
{
  if ( polynome.size( ) == 1 )
  {
    assert( polynome.find( 0 ) != polynome.end( ) );
    return;
  }
  //
  // Get first useful variable
  //
  polynome_t::iterator it = polynome.begin( );
  if ( it->first == 0 ) it ++;
  if ( r == LEQ )
  {
    const Real abs_coeff = ( it->second > 0 ? it->second : -it->second );
    for ( it = polynome.begin( ) ; it != polynome.end( ) ; it ++ ) it->second /= abs_coeff;
  }
  else
  {
    const Real coeff = it->second;
    for ( it = polynome.begin( ) ; it != polynome.end( ) ; it ++ ) it->second /= coeff;
  }

  assert( isCanonized( ) );
}

void LAExpression::addExprWithCoeff( const LAExpression & a, const Real & coeff )
{
  //
  // Iterate over expression to add
  //
  for( polynome_t::const_iterator it = a.polynome.begin( ); it != a.polynome.end( ); it++ )
  {
    polynome_t::iterator it2 = polynome.find( it->first );
    if( it2 != polynome.end( ) )
    {
      it2->second += coeff * it->second;
      if ( it2->first != 0 && it2->second == 0 )
             polynome.erase( it2 );
    }
    else
      polynome[it->first] = coeff * it->second;
  }
}
