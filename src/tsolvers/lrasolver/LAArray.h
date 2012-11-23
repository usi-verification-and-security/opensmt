/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@usi.ch>,
         Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

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

#ifndef LAARRAY_H_
#define LAARRAY_H_

#include "Global.h"

template <class T>
class LAArray : public vector< T >
{
protected:
  unsigned len;          // tracks the quantity of non empty elements
  vector<bool> is_there; // used to perform the fast check if the value is in the row
  vector<int> pool;      // keeps the pool of indexes of empty elements in array

public:
  LAArray( )
  {
    len = 0;
  }

  //
  // Checks by key if an element is in array
  //
  inline bool exists( int key )
  {
    return ( key < ( int )is_there.size( ) && is_there[key] );
  }

  //
  // Quantity of non-empty elements is returned
  //
  inline unsigned size( )
  {
    return len;
  }

  //
  // Returns the position of the next free_element in array
  //
  inline int free_pos( )
  {
    if( pool.empty( ) )
      return vector<T>::size( );
    else
    {
      assert( pool.back( ) >= 0 );
      assert( pool.back( ) < static_cast<int> ( vector<T>::size( ) ) );
      return pool.back( );
    }
  }

  //
  // True if there are no non-empty elements in array
  //
  inline bool empty( )
  {
    return len == 0;
  }

  //
  // Returns iterator to the first non-empty element
  //
  inline typename LAArray<T>::iterator begin( )
  {
    typename LAArray<T>::iterator it = vector<T>::begin( );
    while( it != this->end( ) && it->key == -2 )
    ++it;
    return it;
  }

  //
  // Increases the iterator until next non-empty element
  //
  inline void getNext( typename LAArray<T>::iterator & it )
  {
    ++it;
    while( it != this->end( ) && it->key == -2 )
    ++it;
  }

  //
  // Returns a position in array by iterator
  //
  inline int getPos( typename LAArray<T>::iterator it )
  {
    assert( it - vector<T>::begin( ) >= 0 );
    assert( it - vector<T>::begin( ) < static_cast<int>( vector<T>::size( ) ));
    return ( it - vector<T>::begin( ) );
  }

  //
  // Find iterator to an element by its key
  // Note: checking in is_there is omitted since find should be called when the existence of an element is ensured
  //
  inline typename LAArray<T>::iterator find( int key )
  {
    for( typename LAArray<T>::iterator it = this->begin(); it != this->end( ); this->getNext(it) )
    {
      if( key == it->key )
        return it;
    }
    return this->end( );
  }

  //
  // Erase the element by its position in array
  //
  inline void remove( int pos )
  {
    this->remove(vector<T>::begin() + pos);
  }


  //
  // Erase the element by its iterator
  //
  inline void remove( typename LAArray<T>::iterator it )
  {
    assert( it - vector<T>::begin( ) >= 0 );
    assert( it - vector<T>::begin( ) < static_cast<int>( vector<T>::size( ) ));

    // Check if element is in the this
    int & key = it->key;
    assert( key >= 0);
    assert( key < ( int )is_there.size( ) );
    assert( is_there[key] );
    is_there[key] = false;
    key=-2;
    pool.push_back(it-vector<T>::begin());
    len--;
  }

  //
  // Delete all elements from the this
  //
  inline void clear( )
  {
    for( typename LAArray<T>::iterator it = this->begin( ); it != this->end( ); getNext( it ) )
      this->remove(it);
    assert(len==0);
  }
};

#endif /* LAARRAY_H_ */
