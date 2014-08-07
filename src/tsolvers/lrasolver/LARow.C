/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@usi.ch>,
         Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

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

#include "LARow.h"
//
// Adds element to the Row and return the index of the new element in array
//
int LARow::add( const int key, const int pos, Real * coef )
{
  // perform is_there resize if necessary
  if( key >= ( int )is_there.size( ) )
    is_there.resize( key + 1, false );
  assert( !is_there[key] );

  is_there[key] = true;
  len++;
  if( pool.empty( ) )
  {
    this->push_back( LARowItem( key, pos, coef ) );
    return vector<LARowItem>::size( ) - 1;
  }
  else
  {
    const int i = pool.back( );
    assert( i >= 0 );
    assert( i < static_cast< int >( vector<LARowItem>::size( ) ) );
    pool.pop_back( );
    LARowItem & item = ( *this )[i];
    assert( item.key == -2 );
    item.key = key;
    item.pos = pos;
    item.coef = coef;
    return i;
  }
}
