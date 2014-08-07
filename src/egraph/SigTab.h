/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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
