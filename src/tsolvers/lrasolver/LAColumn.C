/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@usi.ch>,
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

