/*********************************************************************
Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
      , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

OpenSMT -- Copyright (C) 2008-2012, Roberto Bruttomesso

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

#ifndef LAVAR_H
#define LAVAR_H

#include "Global.h"
#include "Enode.h"
#include "Delta.h"
#include "LARow.h"
#include "LAColumn.h"

//
// Class to store the term of constraints as a column of Simplex method tableau
//
class LAVar
{
public:
  // structure to store bound information
  struct LAVarBound
  {
    Enode * e;
    Delta * delta;
    bool bound_type;
    bool reverse;
    bool active;
    LAVarBound( Delta * _delta, Enode * _e, bool _boundType, bool _reverse );
    bool operator==( const LAVarBound &b );
  };

private:
  typedef vector<LAVarBound> VectorBounds; // type for bounds storage

  static Delta plus_inf_bound;            //used for a default +inf value, which is shared by every LAVar
  static Delta minus_inf_bound;           //used for a default -inf value, which is shared by every LAVar

  static int column_count;               // Static counter to create ID for LAVar
  static int row_count;                  // Static counter for rows keep track of basic variables

  static unsigned model_global_counter;   // global counter used to inform all the LAVar if they are different from the last saved point
  unsigned model_local_counter;           // local counter used to decide when the model should be switched

  int column_id;                         // ID (column number) for LAVar
  int row_id;                            // row_id (row number) for LAVar. For public known as basicID :)

  Delta * m1;                           // one of two storages used by model switching
  Delta * m2;                           // one of two storages used by model switching

public:
  Enode * e;             //pointer to original Enode. In case of slack variable points to polynomial
  LARow polynomial;      // elements of the variable polynomial (if variable is basic), list of <id, Real*>
  LAColumn binded_rows;     // rows a variable is binded to (if it is nonbasic) ,list of <id, Real*>
  bool skip;             //used to skip columns deleted during Gaussian
  VectorBounds all_bounds;// array storage for all bounds of the variable
  unsigned u_bound;      // integer pointer to the current upper bound
  unsigned l_bound;      // integer pointer to the current lower bound

  LAVar( Enode * e_orig);                                              // Default constructor
  LAVar( Enode * e_orig, Enode * e_bound, Enode * e_var, bool basic );  // Constructor with bounds
  LAVar( Enode * e_orig, Enode * e_var, const Real & v, bool revert );        // Constructor with bounds from real
  virtual ~LAVar( );                                                    // Destructor

  void setBounds( Enode * e, Enode * e_bound);          // Set the bounds from Enode of original constraint (used on reading/construction stage)
  void setBounds( Enode * e, const Real & v, bool revert);   // Set the bounds according to enode type and a given value (used on reading/construction stage)

  unsigned setUpperBound( const Real & v);
  unsigned setLowerBound( const Real & v);

  unsigned setBound( const Real & v, bool upper);
  void addBoundsAndUpdateSorting(const LAVarBound & pb1, const LAVarBound & pb2);
  void addBoundAndUpdateSorting(const LAVarBound & pb);
  void updateSorting();

  unsigned getBoundByValue( const Real & v, bool upper);

  void sortBounds( );   // sort bounds' list
  void printBounds( );  // print out bounds' list

  void getDeducedBounds( const Delta& c, bool upper, vector<Enode *>& dst, int solver_id );     // find possible deductions by value c
  void getDeducedBounds( bool upper, vector<Enode *>& dst, int solver_id );                     // find possible deductions for actual bounds values
  void getSuggestions( vector<Enode *>& dst, int solver_id );                                   // find possible suggested atoms
  void getSimpleDeductions( vector<Enode *>& dst, bool upper, int solver_id );                  // find deductions from actual bounds position
  unsigned getIteratorByEnode( Enode * e, bool );                                               // find bound iterator by the correspondent Enode ID

  inline bool isBasic( );               // Checks if current LAVar is Basic in current solver state
  inline bool isNonbasic( );            // Checks if current LAVar is NonBasic in current solver state
  inline bool isModelOutOfBounds( );    // Check if current Model for LAVar does not feat into the bounds.
  inline bool isModelOutOfLowerBound( );// Check if current Model for LAVar does not feat into the lower bound.
  inline bool isModelOutOfUpperBound( );// Check if current Model for LAVar does not feat into the upper bound.
  inline bool isUnbounded( );           // Check if LAVar has no bounds at all (it can be eliminated if possible).
  inline bool isModelInteger( );        // Check if LAVar has an integer model.
  inline bool isEquality();
  inline const Delta overBound();

  inline int ID( );                             // Return the ID of the LAVar
  inline int basicID( );                        // Return the basicID (row id) of the basic LAVar (-1 if it is Nonbasic)
  inline void setNonbasic( );                   // Make LAVar Nonbasic
  inline void setBasic( int row );              // Make LAVar Basic and set the row number it corresponds
//  inline void bindRow( int row, Real * a );     // bind current LAVar to a row with an attribute a
  inline void unbindRow( int row );             // remove row from the binding list
  inline void saveModel( );                     // save model locally
  inline void restoreModel( );                  // restore to last globally saved model
  static inline void saveModelGlobal( );        // save model globally
  void computeModel( const Real& b = 0 );       // save the actual model to Egraph

  inline const Delta & U( ); // The latest upper bound of LAVar (+inf by default)
  inline const Delta & L( ); // The latest lower bound of LAVar (-inf by default)
  inline const Delta & M( ); // The latest model of LAVar (0 by default)

  inline void incM( const Delta &v ); // increase actual model by v
  inline void setM( const Delta &v ); //set actual model to v

  // two operators for output
  inline friend ostream & operator <<( ostream & out, LAVar * v )
  {
    if( v->e->isVar( ) || v->e->isUf( ) )
      out << v->e;
    else
      out << "s" << v->ID( );
    return out;
  }
  inline friend ostream & operator <<( ostream & out, LAVar & v )
  {
    out << &v;
    return out;
  }

  // structure to perform comparison of two LAVarBounds
  struct LAVarBounds_ptr_cmp
  {
    bool operator()( LAVarBound lhs, LAVarBound rhs );
  };
};

bool LAVar::isBasic( )
{
  return ( row_id != -1 );
}

bool LAVar::isModelOutOfBounds( )
{
//  if ( M( ) > U( ) || M( ) < L( ) )
//  {
//cout << *this << ": " << L() << " <= " << M() << " <= " << U()<< endl;
//    return true;
//  }
//  else
//    return false;
  return ( M( ) > U( ) || M( ) < L( ) );
}

bool LAVar::isModelOutOfUpperBound( )
{
  return ( M( ) > U( ));
}

bool LAVar::isModelOutOfLowerBound( )
{
  return ( M( ) < L( ));
}


const Delta LAVar::overBound( )
{
  assert( isModelOutOfBounds( ) );
  if( M( ) > U( ) )
  {
    return ( Delta(M( ) - U( )));
  }
  else if ( M( ) < L( ))
  {
    return ( Delta(L( ) - M( )) );
  }
  assert (false);
}


bool LAVar::isModelInteger( )
{
  return !( M( ).hasDelta() || M().R().get_den() != 1);
}

bool LAVar::isEquality( )
{
  if( l_bound + 1 == u_bound && !L( ).isInf( ) && !U( ).isInf( ) && all_bounds[l_bound].delta == all_bounds[u_bound].delta )
    return true;
  else
    return false;
}

bool LAVar::isUnbounded( )
{
  return all_bounds.size( ) < 3;
}

bool LAVar::isNonbasic( )
{
  return !isBasic( );
}

int LAVar::ID( )
{
  return column_id;
}

int LAVar::basicID( )
{
  return row_id;
}

void LAVar::setNonbasic( )
{
  row_id = -1;
}

void LAVar::setBasic( int row )
{
  row_id = row;
}

//void LAVar::bindRow( int row, Real * a )
//{
//  assert( this->binded_rows.find( row ) == this->binded_rows.end( ) );
//  this->binded_rows.add( row, a );
//}

void LAVar::unbindRow( int row )
{
  assert( this->binded_rows.find( row ) != this->binded_rows.end( ) || this->isBasic( ) );
  this->binded_rows.remove( this->binded_rows.find( row ) );
}

void LAVar::saveModel( )
{
  *m2 = *m1;
  model_local_counter = model_global_counter;
}

void LAVar::saveModelGlobal( )
{
  model_global_counter++;
}

void LAVar::restoreModel( )
{
  if( model_local_counter == model_global_counter )
  {
    *m1 = *m2;
    model_local_counter--;
  }
}

const Delta & LAVar::U( )
{
  assert( all_bounds[u_bound].delta );
  return *( all_bounds[u_bound].delta );
}

const Delta & LAVar::L( )
{
  assert( all_bounds[l_bound].delta );
  return *( all_bounds[l_bound].delta );
}

const Delta & LAVar::M( )
{
  return ( *m1 );
}

void LAVar::incM( const Delta &v )
{
  setM( M( ) + v );
}

void LAVar::setM( const Delta &v )
{
  if( model_local_counter != model_global_counter )
    saveModel( );
  ( *m1 ) = v;
}

#endif
