/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

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

#include "LAVar.h"

int LAVar::column_count = 0;
int LAVar::row_count = 0;

Delta LAVar::plus_inf_bound = Delta( Delta::UPPER );
Delta LAVar::minus_inf_bound = Delta( Delta::LOWER );

unsigned LAVar::model_global_counter = 1;

//
// Default constructor
//
LAVar::LAVar( Enode * e_orig = NULL )
{
  column_id = column_count++;
  row_id = -1;
  skip = false;

  // zero as default model
  m1 = new Delta( Delta::ZERO );
  m2 = new Delta( Delta::ZERO );
  model_local_counter = 0;

  Enode * e_null = NULL;
  LAVarBound pb1( &minus_inf_bound, e_null, false, false );
  LAVarBound pb2( &plus_inf_bound, e_null, true, false );
  all_bounds.push_back( pb1 );
  all_bounds.push_back( pb2 );
  u_bound = 1;
  l_bound = 0;

  e = e_orig;
}

//
// Constructor with bounds initialization
//
LAVar::LAVar( Enode * e_orig, Enode * e_bound, Enode * e_var, bool basic = false )
{
  column_id = column_count++;

  if( basic )
    row_id = row_count++;
  else
    row_id = -1;

  skip = false;

  // zero as default model
  m1 = new Delta( Delta::ZERO );
  m2 = new Delta( Delta::ZERO );
  model_local_counter = 0;

  Enode * e_null = NULL;
  LAVarBound pb1( &minus_inf_bound, e_null, false, false );
  LAVarBound pb2( &plus_inf_bound, e_null, true, false );
  all_bounds.push_back( pb1 );
  all_bounds.push_back( pb2 );
  u_bound = 1;
  l_bound = 0;

  e = e_var;
  // set original bounds from Enode
  setBounds( e_orig, e_bound );
}

LAVar::LAVar( Enode * e_orig, Enode * e_var, const Real & v, bool revert )
{
  column_id = column_count++;
  row_id = -1;

  skip = false;

  // zero as default model
  m1 = new Delta( Delta::ZERO );
  m2 = new Delta( Delta::ZERO );
  model_local_counter = 0;

  Enode * e_null = NULL;
  LAVarBound pb1( &minus_inf_bound, e_null, false, false );
  LAVarBound pb2( &plus_inf_bound, e_null, true, false );
  all_bounds.push_back( pb1 );
  all_bounds.push_back( pb2 );
  u_bound = 1;
  l_bound = 0;

  e = e_var;

  // set original bounds from Enode
  setBounds( e_orig, v, revert );

}

LAVar::~LAVar( )
{
  // Remove bounds
  while( !all_bounds.empty( ) )
  {
    assert( all_bounds.back( ).delta );
    if( all_bounds.back( ).delta != &minus_inf_bound && all_bounds.back( ).delta != &plus_inf_bound )
      delete all_bounds.back( ).delta;
    all_bounds.pop_back( );
  }
  // Remove polynomial coefficients
  for( LARow::iterator it = polynomial.begin( ); it != polynomial.end( ); polynomial.getNext( it ) )
  {
    assert( it->coef );
    if( it->key != -2 )
      delete it->coef;
    //    it->second = NULL;
  }

  delete ( m2 );
  delete ( m1 );
}

//TODO: more intelligent value parsing would be nice.
//
// Parse the bound value and the type of the constraint
//
void LAVar::setBounds( Enode * e, Enode * e_bound )
{
  assert( e->isAtom( ) );
  assert( e_bound->isConstant( ) );

  bool revert = false;

  if( !( e->get1st( )->isConstant( ) ) )
    revert = true;

  if( e_bound->isConstant( ) )
    setBounds( e, e_bound->getComplexValue( ), revert );
  else
    opensmt_error2( "unexpected Num: ", e_bound );
}

//
// Reads the type of the bounds from enode type
//
void LAVar::setBounds( Enode * e, const Real & v, bool revert )
{

  assert( e->isLeq( ) );

  Delta * bound = NULL;
  Delta * boundRev = NULL;

  Delta::deltaType bound_type = Delta::UPPER;

  bound = new Delta( v );

  if( revert )
  {
    boundRev = new Delta( v, 1 );
  }
  else
  {
    boundRev = new Delta( v, -1 );
    bound_type = Delta::LOWER;
  }

  assert( bound );
  assert( boundRev );
  assert( bound != boundRev );

  LAVarBound pb1( bound, e, ( bound_type == Delta::UPPER ), false );
  LAVarBound pb2( boundRev, e, ( bound_type != Delta::UPPER ), true );

  addBoundsAndUpdateSorting( pb1, pb2 );
}

unsigned LAVar::setUpperBound( const Real & v )
{
  return setBound( v, true );
}

unsigned LAVar::setLowerBound( const Real & v )
{
  return setBound( v, false );
}

unsigned LAVar::setBound( const Real & v, bool upper )
{
  unsigned i = getBoundByValue( v, upper );
  if( i != 0 )
    return i;

  Delta * bound = NULL;

  Delta::deltaType bound_type = ( upper ? Delta::UPPER : Delta::LOWER );

  bound = new Delta( v );

  assert( bound );

  LAVarBound pb( bound, NULL, ( bound_type == Delta::UPPER ), false );

  addBoundAndUpdateSorting( pb );
  return getBoundByValue( v, upper );
}

void LAVar::addBoundsAndUpdateSorting( const LAVarBound & pb1, const LAVarBound & pb2 )
{
  all_bounds.push_back( pb1 );
  all_bounds.push_back( pb2 );

  updateSorting( );
}

void LAVar::addBoundAndUpdateSorting( const LAVarBound & pb )
{
  all_bounds.push_back( pb );

  updateSorting( );
}

void LAVar::updateSorting( )
{
  // save currently active bounds
  assert( all_bounds.size( ) > 1 && u_bound < all_bounds.size( ) && l_bound < all_bounds.size( ) );

  all_bounds[u_bound].active = true;
  all_bounds[l_bound].active = true;

  //TODO: Instead of sorting all bounds after insertion,
  //      I should check if it fits on left(right) of current pointers and sort only there
  sortBounds( );
  //  printBounds();

  int i;
  // restore lower bound
  if( all_bounds[l_bound].active )
  {
    all_bounds[l_bound].active = false;
  }
  else
  {
    for( i = 0; i < static_cast<int> ( all_bounds.size( ) ); ++i )
    {
      if( !all_bounds[i].bound_type && all_bounds[i].active )
      {
        l_bound = i;
        all_bounds[i].active = false;
        break;
      }
    }
    assert( i != static_cast<int> ( all_bounds.size( ) ) );
  }

  // restore upper bound
  if( all_bounds[u_bound].active )
  {
    all_bounds[u_bound].active = false;
  }
  else
  {
    for( i = all_bounds.size( ) - 1; i >= 0; --i )
    {
      if( all_bounds[i].bound_type && all_bounds[i].active )
      {
        u_bound = i;
        all_bounds[u_bound].active = false;
        break;
      }
    }
    assert( i != 0 );
  }

}

//
// Finds the upper (lower) bounds that are deduced by existing bounds values
//
void LAVar::getDeducedBounds( bool upper, vector<Enode *>& dst, int solver_id )
{
  getDeducedBounds( upper ? U( ) : L( ), upper, dst, solver_id );
}

//
// Finds the upper (lower) bounds that are deduced by a given bound value c
//
void LAVar::getDeducedBounds( const Delta& c, bool upper, vector<Enode *>& dst, int solver_id )
{
  // check upper bound deductions
  if( upper )
  {
    int it = u_bound - 1;
    // everything from the up-most bound until c is deduced (if wasn't before)
    while( ( *( all_bounds[it].delta ) ) >= c )
    {
      if( all_bounds[it].bound_type && all_bounds[it].e != NULL && !all_bounds[it].e->hasPolarity( ) && !all_bounds[it].e->isDeduced( ) )
      {
        all_bounds[it].e->setDeduced( ( all_bounds[it].reverse ? l_False : l_True ), solver_id );
        dst.push_back( all_bounds[it].e );
      }
      it--;
    }
  }
  // check lower bound deductions
  else
  {
    int it = l_bound + 1;
    // everything from the low-most bound until c is deduced (if wasn't before)
    while( ( *( all_bounds[it].delta ) ) <= c )
    {
      if( !all_bounds[it].bound_type && !all_bounds[it].e->hasPolarity( ) && !all_bounds[it].e->isDeduced( ) )
      {
        all_bounds[it].e->setDeduced( ( all_bounds[it].reverse ? l_False : l_True ), solver_id );
        dst.push_back( all_bounds[it].e );
      }
      it++;
    }
  }
}

//
// Deduces anything upper (lower) the actual bounds for this LAVar
//
void LAVar::getSimpleDeductions( vector<Enode *>& dst, bool upper, int solver_id )
{
  if( !upper && !all_bounds[l_bound].delta->isInf( ) )
  {
    assert( l_bound > 0 );
    // everything from the low-most bound until actual is deduced (if wasn't before)
    for( int it = l_bound - 1; it > 0; it-- )
    {
      if( !all_bounds[it].bound_type && all_bounds[it].e != NULL && !all_bounds[it].e->hasPolarity( ) && !all_bounds[it].e->isDeduced( ) )
      {
        all_bounds[it].e->setDeduced( ( all_bounds[it].reverse ? l_False : l_True ), solver_id );
        dst.push_back( all_bounds[it].e );
        //        cout  << "Deduced from lower " << all_bounds[it].e << endl;
      }
    }
  }

  if( upper && !all_bounds[u_bound].delta->isInf( ) )
  {
    // everything from the up-most bound until actual is deduced (if wasn't before)
    for( int it = u_bound + 1; it < static_cast<int> ( all_bounds.size( ) ) - 1; it++ )
    {
      if( all_bounds[it].bound_type && all_bounds[it].e != NULL && !all_bounds[it].e->hasPolarity( ) && !all_bounds[it].e->isDeduced( ) )
      {
        all_bounds[it].e->setDeduced( ( all_bounds[it].reverse ? l_False : l_True ), solver_id );
        dst.push_back( all_bounds[it].e );
        //        cout  << "Deduced from upper as " << (all_bounds[it].reverse ? "FALSE " : "TRUE ") << all_bounds[it].e << endl;
      }
    }
  }
}

//
// Proposes bounds and their polarity for main solver
//
void LAVar::getSuggestions( vector<Enode *>& dst, int solver_id )
{
  ( void )solver_id;
  if( M( ) > U( ) )
  {
    all_bounds[u_bound].e->setDecPolarity( all_bounds[u_bound].reverse );
    dst.push_back( all_bounds[u_bound].e );
  }
  else if( M( ) < L( ) )
  {
    all_bounds[l_bound].e->setDecPolarity( all_bounds[l_bound].reverse );
    dst.push_back( all_bounds[l_bound].e );
  }
}

//
// Finds the bound from the bound list that correspond to the given Enode and polarity
//
//TODO:: Can I do better here? Iterate from different sides? - YES
unsigned LAVar::getIteratorByEnode( Enode * _e, bool _reverse )
{
  unsigned it;
  it = all_bounds.size( ) - 2;
  assert( it != 0 );
  while( it > 0 && !( all_bounds[it].e == _e && all_bounds[it].reverse == _reverse ) )
    --it;
  assert( it != 0 ); // we assume Enode is in!
  return it;
}

unsigned LAVar::getBoundByValue( const Real & v, bool upper )
{
  unsigned it = all_bounds.size( ) - 2;
  assert( it != 0 );
  while( it > 0 && !( all_bounds[it].delta->R( ) == v && all_bounds[it].bound_type == upper ) )
    --it;
  return it;
}

//
// Sorts the bounds on the list
//
void LAVar::sortBounds( )
{
  sort( all_bounds.begin( ), all_bounds.end( ), LAVarBounds_ptr_cmp( ) );

  u_bound = all_bounds.size( ) - 1;
  l_bound = 0;

}

//
// Computes the model and pushes it to the correspondent Enode (delta is taken into account)
//
void LAVar::computeModel( const Real& d )
{
  assert( !isModelOutOfBounds( ) );
  this->e->setValue( M( ).R( ) + d * M( ).D( ) );
}

//
// Prints the bounds of the LAVar
//
void LAVar::printBounds( )
{
  cerr << endl << this << " | ";
  for( unsigned i = 0; i < all_bounds.size( ); i++ )
    cerr << *( all_bounds[i].delta ) << ( all_bounds[i].bound_type ? "[U]" : "[L]" ) << ( all_bounds[i].reverse ? "rev" : "" ) << " ";
}

bool LAVar::LAVarBounds_ptr_cmp::operator()( LAVarBound lhs, LAVarBound rhs )
{
  assert( lhs.delta );
  assert( rhs.delta );
  if( lhs == rhs )
    return true;
  else if( !lhs.delta->isInf( ) && !rhs.delta->isInf( ) && lhs.delta->R( ) == rhs.delta->R( ) )
  {
    if( lhs.bound_type == rhs.bound_type )
    {
      // if this assertion fails then you have duplicates in the bounds list. Check the canonizer.
      assert( lhs.delta->D( ) != rhs.delta->D( ) );
      if( lhs.bound_type )
        return ( lhs.delta->D( ) == 1 || lhs.delta->D( ) == -1 );
      else
        return ( lhs.delta->D( ) == 0 );
    }
    else if( lhs.bound_type )
      return ( lhs.delta->D( ) == 1 || lhs.delta->D( ) == -1 || rhs.delta->D( ) == 1 );
    else
      return ( lhs.delta->D( ) == 0 && rhs.delta->D( ) == 0 );
  }
  else
    return *( lhs.delta ) < *( rhs.delta );
}

LAVar::LAVarBound::LAVarBound( Delta * _delta, Enode * _e, bool _boundType, bool _reverse )
{
  delta = _delta;
  e = _e;
  bound_type = _boundType;
  reverse = _reverse;
  active = false;
}

bool LAVar::LAVarBound::operator==( const LAVarBound &b )
{
  if( ( this->e == b.e ) && ( this->delta == b.delta ) && ( this->bound_type == b.bound_type ) && ( this->reverse == b.reverse ) )
    return true;
  else
    return false;
}
