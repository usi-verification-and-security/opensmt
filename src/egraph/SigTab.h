/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

//
// Specialized map for pair of integers
//
#ifndef SIG_TAB_H
#define SIG_TAB_H

#include "Enode.h"

#define SIG_TAB_INITIAL_SIZE 1024
#define CACHE_SIZE           3

class SigTab
{
public:

   SigTab( );
  ~SigTab( );

  Enode * insert ( const enodeid_t, Enode *, Enode * );  // Insert and creates node if not there
  Enode * insert ( Enode * );                            // Inserts a symbol
  void    erase  ( Enode * );                            // Erase a pair
#ifdef BUILD_64
  Enode * lookup ( const enodeid_pair_t & );             // Lookup an enode by signature
#else
  Enode * lookup ( const Pair( enodeid_t ) & );          // Lookup an enode by signature

  struct Cell
  {
    Enode * elem;
    bool    active;
    // int     second;
  };
#endif

  void initialize        ( vector< int > & );
  void printStatistics   ( ostream &, int * );
#if PEDANTIC_DEBUG
  bool checkInvariantSTC ( );
#endif

private:

#ifdef BUILD_64
  typedef hash_map< enodeid_pair_t, Enode * > HashTable;       // Hash Table type
  HashTable                                   store;           // Store
#else                                         
  typedef hash_map< enodeid_t, Cell * >       HashTable;       // Hash Table type
  vector< HashTable * >                       store;           // The actual store 
  vector< Cell * >		              cells;           // Collects cells for deletion
#endif                                        
  bool                                        initialized;     // Has it been initialized ?

};

#endif
