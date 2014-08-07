/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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

#include "SigTab.h"

SigTab::SigTab( )
{
#ifdef BUILD_64
#else
  store.resize( SIG_TAB_INITIAL_SIZE, NULL );
#endif
  initialized = true;
}

SigTab::~SigTab( )
{
#ifdef BUILD_64
#else
  while ( !store.empty( ) )
  {
    if ( store.back( ) != NULL )
      delete store.back( );
    store.pop_back( );
  }
  while ( !cells.empty( ) )
  {
    assert( cells.back( ) );
    delete cells.back( );
    cells.pop_back( );
  }
#endif
}

Enode * SigTab::insert ( const enodeid_t id, Enode * car, Enode * cdr )
{
  assert( initialized );
  assert( car == car->getRoot( ) );
  assert( cdr == cdr->getRoot( ) );

  enodeid_t first  = cdr->isEnil( ) ? car->getCid( ) : cdr->getCid( );
  enodeid_t second = cdr->isEnil( ) ? cdr->getCid( ) : car->getCid( );

  Enode * ret_value = NULL;

#ifdef BUILD_64
  (void)id;
  enodeid_pair_t key = encode( first, second );
  ret_value = store[ key ];
#else
  // Enlarge store if necessary
  if ( (int)store.size( ) <= first )
    store.resize( first + 1, NULL );
  // Allocates hash map if not present
  if ( store[ first ] == NULL )
    store[ first ] = new HashTable;
  HashTable & ht = *(store[ first ]);
  // Seek second
  HashTable::iterator it = ht.find( second );
  // There is a previous entry,
  // It might be either active or inactive
  if ( it != ht.end( ) )
  {
    Cell * c = (Cell *)it->second;
    assert( c->active );
    // If the entry is active, then no insertion
    // takes place, and we leave the previous element
    // there
    if ( c->active )
    {
      ret_value = c->elem;
    }
    // Otherwise we make this entry active
    // and we replace the corresponding element
    else
    {
      c->active = true;
      Enode * e = new Enode( id, car, cdr );   
      c->elem = e;
      ret_value = e;
    }
  }
  // Otherwise there is no entry for this 
  // data, we create a new one and make it active
  else
  {
    Cell * cell = new Cell;
    cells.push_back( cell );
    cell->elem = new Enode( id, car, cdr );   
    cell->active = true;
    ht[ second ] = cell;
    ret_value = cell->elem;
  }
#endif
  assert( ret_value );
  return ret_value;
}

Enode * SigTab::insert ( Enode * data )
{
  assert( initialized );
  const enodeid_t first  = data->getSigCar( );
  const enodeid_t second = data->getSigCdr( );

#ifdef BUILD_64
  enodeid_pair_t key = encode( first, second );
  pair< HashTable::iterator, bool > it = store.insert( make_pair( key, data ) );
  if ( it.second )
    return data;
  return (*(it.first)).second;
#else
  // Enlarge store if necessary
  if ( (int)store.size( ) <= first )
    store.resize( first + 1, NULL );
  // Allocates hash map if not present
  if ( store[ first ] == NULL )
    store[ first ] = new HashTable;
  HashTable & ht = *(store[ first ]);
  // Seek second
  HashTable::iterator it = ht.find( second );
  Enode * ret_value = NULL;
  // There is a previous entry,
  // It might be either active or inactive
  if ( it != ht.end( ) )
  {
    Cell * c = (Cell *)it->second;
    // If the entry is active, then no insertion
    // takes place, and we leave the previous element
    // there
    if ( c->active )
    {
      ret_value = c->elem;
    }
    // Otherwise we make this entry active
    // and we replace the corresponding element
    else
    {
      c->active = true;
      c->elem = data;
      ret_value = data;
    }
  }
  // Otherwise there is no entry for this 
  // data, we create a new one and make it active
  else
  {
    Cell * cell = new Cell;
    cells.push_back( cell );
    cell->elem = data;
    cell->active = true;
    ht[ second ] = cell;
    ret_value = data;
  }
  assert( ret_value );

  return ret_value;
#endif
}

//
// TODO: change this erase to stack-based erase:
// since elements are deleted stack-based we can
// just pop the last pushed cell and deactivate it
// 
// or is insert stack-based ?
//
void SigTab::erase ( Enode * p )
{
  assert( initialized );
  const enodeid_t first  = p->getSigCar( );
  const enodeid_t second = p->getSigCdr( );

#ifdef BUILD_64
  enodeid_pair_t key = encode( first, second );
  HashTable::iterator it = store.find( key ); 
  assert( it != store.end( ) );
  store.erase( it );
#else
  // Make sure it exists
  assert( first < (int)store.size( ) );
  HashTable & ht = *(store[ first ]);
  HashTable::iterator it = ht.find( second );
  assert( it != ht.end( ) );
  Cell * c = ((Cell *)it->second);
  c->active = false;
#endif
}

#ifdef BUILD_64
Enode * SigTab::lookup ( const enodeid_pair_t & p )
{
  HashTable::iterator it = store.find( p ); 
  if ( it == store.end( ) )
    return NULL;
  return it->second;
}
#else
Enode * SigTab::lookup ( const Pair( int ) & p )
{
  assert( initialized );
  const enodeid_t first  = p.first;
  const enodeid_t second = p.second;
  // The first element is not there
  if ( first >= (int)store.size( ) )
    return NULL;
  // The first is there but no second
  if ( store[ first ] == NULL )
    return NULL;
  // The first is there but no second
  HashTable::iterator it = store[ first ]->find( second );
  if ( it == store[ first ]->end( ) )
    return NULL;
  // First and second are there, but not active
  if ( !it->second->active ) 
    return NULL;

  return it->second->elem;
}
#endif

#ifdef BUILD_64
void
SigTab::printStatistics( ostream &, int * )
{ 
  assert( false );
}
#else
void
SigTab::printStatistics( ostream & os, int * maximal )
{
  unsigned max = 0, min = 0xFFFFFFFF, total = 0, elem = 0
         , over1000 = 0, over100 = 0, over10000 = 0, over10 = 0
	 , over5 = 0, one = 0, two = 0, thr = 0, fou = 0, fiv = 0;
  for ( unsigned i = 0 ; i < store.size( ) ; i ++ )
  {
    if ( store[ i ] == NULL )
      continue;
    elem ++;

    total += store[ i ]->size( );
    if ( max < store[ i ]->size( ) )
    {
      max = store[ i ]->size( );
      *maximal = i;
    }
    if ( min > store[ i ]->size( ) )
      min = store[ i ]->size( );
    if ( store[ i ]->size( ) == 1 ) one ++;
    if ( store[ i ]->size( ) == 2 ) two ++;
    if ( store[ i ]->size( ) == 3 ) thr ++;
    if ( store[ i ]->size( ) == 4 ) fou ++;
    if ( store[ i ]->size( ) == 5 ) fiv ++;
    if ( store[ i ]->size( ) > 5 ) over5 ++;
    if ( store[ i ]->size( ) > 10 ) over10 ++;
    if ( store[ i ]->size( ) > 100 ) over100 ++;
    if ( store[ i ]->size( ) > 1000 ) over1000 ++;
    if ( store[ i ]->size( ) > 10000 ) over10000 ++;
  }

  os << "#" << endl;
  os << "# Total cells...: " << store.size( ) << endl;
  os << "# Actual cells..: " << elem << endl;
  os << "# Min size......: " << min << endl;
  os << "# Max size......: " << max << endl;
  os << "# One...........: " << one << endl;
  os << "# Two...........: " << two << endl;
  os << "# Thr...........: " << thr << endl;
  os << "# Fou...........: " << fou << endl;
  os << "# Fiv...........: " << fiv << endl;
  os << "# Over 5........: " << over5 << endl;
  os << "# Over 10.......: " << over10 << endl;
  os << "# Over 100......: " << over100 << endl;
  os << "# Over 1000.....: " << over1000 << endl;
  os << "# Over 10000....: " << over10000 << endl;
  os << "# Avg size......: " << total / ( 1.0 * elem ) << endl;
  os << "#" << endl;
}
#endif
