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

#include "LAColumn.h"

int LAColumn::add( const int key, const int pos )
{
  // perform is_there resize if necessary
  if( key >= ( int )is_there.size( ) )
    is_there.resize( key + 1, false );
  assert( !is_there[key] );

  is_there[key] = true;
  len++;
  if( pool.empty( ) )
  {
    this->push_back( LAColumnItem( key, pos ) );
    return vector<LAColumnItem>::size( ) - 1;
  }
  else
  {
    const int i = pool.back( );
    assert( i >= 0 );
    assert( i < static_cast< int >( vector<LAColumnItem>::size( ) ) );
    pool.pop_back( );
    LAColumnItem & item = ( *this )[i];
    assert( item.key == -2 );
    item.key = key;
    item.pos_in_row = pos;
    return i;
  }
}

