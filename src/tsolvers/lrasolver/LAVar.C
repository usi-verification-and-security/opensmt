/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 Antti Hyvarinen <antti.hyvarinen@gmail.com>

 OpenSMT2 -- Copyright (C) 2012 - 2015, Antti Hyvarinen
                           2008 - 2012, Roberto Bruttomesso

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

#include "LRASolver.h"

const char* const BoundT::names[3] = {"[L]", "[U]", "[N]"};

Delta LAVar::plus_inf_bound = Delta( Delta::UPPER );
Delta LAVar::minus_inf_bound = Delta( Delta::LOWER );

unsigned LAVar::model_global_counter = 1;

//
// Default constructor
//
LAVar::LAVar(LRASolver& lra, SolverId sid, vec<DedElem>& d, LRALogic& l, int column_id, PTRef e_orig = PTRef_Undef)
	: logic(l)
	, deduced(d)
	, solver_id(sid)
	, lra_solver(lra)
        , column_id(column_id)
{
//  column_id = column_count++;
  row_id = -1;
  skip = false;

  // zero as default model
  m1 = new Delta( Delta::ZERO );
  m2 = new Delta( Delta::ZERO );
  model_local_counter = 0;

  PTRef e_null = PTRef_Undef;
  LAVarBound pb1( &minus_inf_bound, e_null, bound_l, false );
  LAVarBound pb2( &plus_inf_bound, e_null, bound_u, false );
  all_bounds.push_back( pb1 );
  all_bounds.push_back( pb2 );
  u_bound = 1;
  l_bound = 0;

  e = e_orig;
}

//
// Constructor with bounds initialization
//
LAVar::LAVar(LRASolver& lra, SolverId sid, vec<DedElem>& d, LRALogic& l, PTRef e_orig, PTRef e_bound, PTRef e_var, int column_id, int row_id)
        : logic(l)
        , deduced(d)
        , solver_id(sid)
        , lra_solver(lra)
        , column_id(column_id)
        , row_id(row_id)
{
//  column_id = column_count++;
//
//  if( basic )
//    row_id = row_count++;
//  else
//    row_id = -1;

  skip = false;

  // zero as default model
  m1 = new Delta( Delta::ZERO );
  m2 = new Delta( Delta::ZERO );
  model_local_counter = 0;

  PTRef e_null = PTRef_Undef;
  LAVarBound pb1( &minus_inf_bound, e_null, bound_l, false );
  LAVarBound pb2( &plus_inf_bound, e_null, bound_u, false );
  all_bounds.push_back( pb1 );
  all_bounds.push_back( pb2 );
  u_bound = 1;
  l_bound = 0;

  e = e_var;
  // set original bounds from Enode
  setBounds( e_orig, e_bound );
}

//LAVar::LAVar(LRASolver& lra, SolverId sid, vec<DedElem>& d, LRALogic& l, PTRef e_orig, PTRef e_var, int column_id, const Real & v, bool revert )
//	: logic(l)
//	, deduced(d)
//	, solver_id(sid)
//	, lra_solver(lra)
//        , column_id(column_id)
//{
////  column_id = column_count++;
//  row_id = -1;
//
//  skip = false;
//
//  // zero as default model
//  m1 = new Delta( Delta::ZERO );
//  m2 = new Delta( Delta::ZERO );
//  model_local_counter = 0;
//
//  PTRef e_null = PTRef_Undef;
//  LAVarBound pb1( &minus_inf_bound, e_null, bound_l, false );
//  LAVarBound pb2( &plus_inf_bound, e_null, bound_u, false );
//  all_bounds.push_back( pb1 );
//  all_bounds.push_back( pb2 );
//  u_bound = 1;
//  l_bound = 0;
//
//  e = e_var;
//
//  // set original bounds from Enode
//  setBounds( e_orig, v, revert );
//
//}

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
void LAVar::setBounds( PTRef e, PTRef e_bound, bool revert )
{
    assert( logic.isAtom(e) );
    assert( logic.isConstant(e_bound) );


    if (!(logic.isConstant(logic.getPterm(e)[0])))
        revert != revert;

    setBounds( e, logic.getRealConst(e_bound), revert );
}

//
// Reads the type of the bounds from enode type
//
void LAVar::setBounds( PTRef e, const Real & v, bool revert )
{

  assert( logic.isRealLeq(e) );

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

  LAVarBound pb1( bound, e, ( bound_type == Delta::UPPER ) ? bound_u : bound_l, false );
  LAVarBound pb2( boundRev, e, ( bound_type != Delta::UPPER ) ? bound_u : bound_l, true );

  addBoundsAndUpdateSorting( pb1, pb2 );
}

unsigned LAVar::setUpperBound( const Real & v )
{
  return setBound(v, bound_u);
}

unsigned LAVar::setLowerBound( const Real & v )
{
  return setBound(v, bound_l);
}

unsigned LAVar::setBound(const Real & v, BoundT b)
{
  unsigned i = getBoundByValue( v, b );
  if( i != 0 )
    return i;

  Delta * bound = NULL;

  bound = new Delta( v );

  assert( bound );

  LAVarBound pb( bound, PTRef_Undef, b, false );

  addBoundAndUpdateSorting( pb );
  return getBoundByValue(v, b);
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
      if( (all_bounds[i].bound_type == bound_l) && all_bounds[i].active )
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
      if( (all_bounds[i].bound_type == bound_u) && all_bounds[i].active )
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
void LAVar::getDeducedBounds( BoundT b, vec<PtAsgn_reason>& dst, SolverId solver_id )
{
  getDeducedBounds( b == bound_u ? U( ) : L( ), b, dst, solver_id );
}

//
// Finds the upper (lower) bounds that are deduced by a given bound value c
//
void LAVar::getDeducedBounds( const Delta& c, BoundT b, vec<PtAsgn_reason>& dst, SolverId solver_id )
{
  // check upper bound deductions
  if (b == bound_u)
  {
    int it = u_bound - 1;
    // everything from the up-most bound until c is deduced (if wasn't before)
    while( ( *( all_bounds[it].delta ) ) >= c )
    {
      if( (all_bounds[it].bound_type == bound_u) && all_bounds[it].e != PTRef_Undef && !lra_solver.hasPolarity(all_bounds[it].e) && deduced[logic.getPterm(all_bounds[it].e).getVar()] == l_Undef)
      {
        lbool pol = all_bounds[it].reverse ? l_False : l_True;
        deduced[logic.getPterm(all_bounds[it].e).getVar()] = DedElem(solver_id, pol);
        dst.push(PtAsgn_reason(all_bounds[it].e, pol, PTRef_Undef));
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
      if( (all_bounds[it].bound_type == bound_l) && all_bounds[it].e != PTRef_Undef && !lra_solver.hasPolarity(all_bounds[it].e) && deduced[logic.getPterm(all_bounds[it].e).getVar()] == l_Undef )
      {
        lbool pol = all_bounds[it].reverse ? l_False : l_True;
        deduced[logic.getPterm(all_bounds[it].e).getVar()] = DedElem(solver_id, pol);
        dst.push(PtAsgn_reason(all_bounds[it].e, pol, PTRef_Undef));
      }
      it++;
    }
  }
}

//
// Deduces anything upper (lower) the actual bounds for this LAVar
//
void LAVar::getSimpleDeductions( vec<PtAsgn_reason>& dst, BoundT b, SolverId solver_id )
{
  if( (b == bound_l) && !all_bounds[l_bound].delta->isInf( ) )
  {
    assert( l_bound > 0 );
    // everything from the low-most bound until actual is deduced (if wasn't before)
    for( int it = l_bound - 1; it > 0; it-- )
    {
      if( (all_bounds[it].bound_type == bound_l) && all_bounds[it].e != PTRef_Undef && !lra_solver.hasPolarity(all_bounds[it].e) && deduced[logic.getPterm(all_bounds[it].e).getVar()] == l_Undef)
      {
        lbool pol = all_bounds[it].reverse ? l_False : l_True;
        deduced[logic.getPterm(all_bounds[it].e).getVar()] = DedElem(solver_id, pol);
        dst.push(PtAsgn_reason(all_bounds[it].e, pol, PTRef_Undef));
      }
    }
  }

  if( (b == bound_u) && !all_bounds[u_bound].delta->isInf( ) )
  {
    // everything from the up-most bound until actual is deduced (if wasn't before)
    for( int it = u_bound + 1; it < static_cast<int> ( all_bounds.size( ) ) - 1; it++ )
    {
      if( (all_bounds[it].bound_type == bound_u) && all_bounds[it].e != PTRef_Undef && !lra_solver.hasPolarity(all_bounds[it].e) && deduced[logic.getPterm(all_bounds[it].e).getVar()] == l_Undef)
      {
        lbool pol = all_bounds[it].reverse ? l_False : l_True;
        deduced[logic.getPterm(all_bounds[it].e).getVar()] = DedElem(solver_id, pol);
        dst.push(PtAsgn_reason(all_bounds[it].e, pol, PTRef_Undef));
      }
    }
  }
}

//
// Proposes bounds and their polarity for main solver
//
void LAVar::getSuggestions( vec<PTRef>& dst, SolverId solver_id )
{
/*
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
  */
}

//
// Finds the bound from the bound list that correspond to the given PTRef and polarity
//
//TODO:: Can I do better here? Iterate from different sides? - YES
unsigned LAVar::getIteratorByPTRef( PTRef _e, bool _reverse )
{
  unsigned it;
  it = all_bounds.size() - 2;
  assert( it != 0 );
  while (it > 0 && !( all_bounds[it].e == _e && all_bounds[it].reverse == _reverse ))
    --it;
  assert( it != 0 ); // we assume Enode is in!
  return it;
}

unsigned LAVar::getBoundByValue(const Real & v, BoundT)
{
/*
  unsigned it = all_bounds.size( ) - 2;
  assert( it != 0 );
  while( it > 0 && !( all_bounds[it].delta->R( ) == v && all_bounds[it].bound_type == upper ) )
    --it;
  return it;
*/
      return 0;
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
}

//
// Prints the bounds of the LAVar
//
void LAVar::printBounds( )
{
    std::cerr << "; " << std::endl << "; " << this << " | ";
    for( unsigned i = 0; i < all_bounds.size( ); i++ )
        std::cerr << *( all_bounds[i].delta ) << all_bounds[i].bound_type << ( all_bounds[i].reverse ? "rev" : "" ) << " ";
    if (all_bounds.size() > 0)
        cerr << endl;
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
      if (lhs.bound_type == bound_u)
        return ( lhs.delta->D( ) == 1 || lhs.delta->D( ) == -1 );
      else
        return ( lhs.delta->D( ) == 0 );
    }
    else if (lhs.bound_type == bound_u)
      return ( lhs.delta->D( ) == 1 || lhs.delta->D( ) == -1 || rhs.delta->D( ) == 1 );
    else
      return ( lhs.delta->D( ) == 0 && rhs.delta->D( ) == 0 );
  }
  else
    return *( lhs.delta ) < *( rhs.delta );
}

LAVar::LAVarBound::LAVarBound( Delta * _delta, PTRef _e, BoundT _boundType, bool _reverse )
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

LAVarStore::LAVarStore(LRASolver& lra, vec<DedElem>& d, LRALogic& l)
        : column_count(0)
        , row_count(0)
        , logic(l)
        , deduced(d)
        , solver_id(lra.getId())
        , lra_solver(lra) {}

LAVar* LAVarStore::getNewVar(PTRef e_orig) {
    int column_id = column_count++;
    LAVar* var = new LAVar(lra_solver, solver_id, deduced, logic, column_id, e_orig);
    lavars.push(var);
    return var;
}

LAVar* LAVarStore::getNewVar(PTRef e_orig, PTRef e_bound, PTRef e_var, bool basic) {
    int column_id = column_count++;
    int row_id = basic ? row_count++ : -1;
    LAVar* var = new LAVar(lra_solver, solver_id, deduced, logic, e_orig, e_bound, e_var, column_id, row_id);
    lavars.push(var);
    return var;
}

//LAVar* LAVarStore::getNewVar(PTRef e_orig, PTRef e_var, const Real& v, bool revert) {
//    int column_id = column_count++;
//    LAVar* var = new LAVar(lra_solver, solver_id, deduced, logic, e_orig, e_var, column_id, v, revert);
//    lavars.push(var);
//    return var;
//}

int LAVarStore::numVars() const { return column_count; }

void LAVarStore::printVars() const
{
    for (int i = 0; i < lavars.size(); i++)
        cerr << lavars[i];
}

LAVarStore::~LAVarStore()
{
//    printVars();
}
