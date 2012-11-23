/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

#ifndef SNODE_H
#define SNODE_H

#include "Global.h"
#include "Otl.h"

//
// Predefined snodes id
//
#define SNODE_ID_UNDEF      (-1)  // Undefined sort
#define SNODE_ID_SNIL        (0)  // Empty list
#define SNODE_ID_DOT         (1)  // To create sorts of arity > 0
#define SNODE_ID_BOOL        (2) 
#define SNODE_ID_REAL        (3) 
#define SNODE_ID_INT         (4)
#define SNODE_ID_ARRAY       (5)
#define SNODE_ID_COST        (6)
#define SNODE_ID_BITVEC      (7)
#define SNODE_ID_LAST        (7)
//
// Snode type
//
enum stype_t 
{ 
   STYPE_UNDEF    = 0x00000000 // 0000 0000 0000 0000 0000 0000 0000 0000
 , STYPE_SYMB     = 0x10000000 // 0001 0000 0000 0000 0000 0000 0000 0000
 , STYPE_PARA     = 0x20000000 // 0001 0000 0000 0000 0000 0000 0000 0000
 , STYPE_LIST     = 0x30000000 // 0011 0000 0000 0000 0000 0000 0000 0000
 , STYPE_TERM     = 0x40000000 // 0100 0000 0000 0000 0000 0000 0000 0000
};

#define STYPE_MASK  0xF0000000 // 1111 0000 0000 0000 0000 0000 0000 0000
#define SARITY_N    0x08000000 // 0000 1000 0000 0000 0000 0000 0000 0000
#define SARITY_MASK 0x07F00000 // 0000 0111 1111 0000 0000 0000 0000 0000
#define SARITY_SHIFT 20
#define SMAX_ARITY  (SARITY_MASK >> SARITY_SHIFT)

class Snode
{
public:
  //
  // Constructor for Snil
  //
  Snode  ( );
  //
  // Constructor for symbols
  //
  Snode ( const snodeid_t       // id
        , const char *          // name/value
	, const bool = false    // Is parameter ?
        );
  //
  // Constructor for terms and lists
  //
  Snode ( const snodeid_t       // id
        , Snode *               // car
        , Snode *               // cdr
        );
  //
  // Destructor
  //
  ~Snode ( );
  //
  // Check if a node is Snil
  //
  inline bool isSnil            ( ) const { return id == SNODE_ID_SNIL; }
  inline bool isList            ( ) const { return (properties & STYPE_MASK) == STYPE_LIST; }
  inline bool isTerm            ( ) const { return (properties & STYPE_MASK) == STYPE_TERM; }
  inline bool isSymb            ( ) const { return (properties & STYPE_MASK) == STYPE_SYMB; }
  inline bool isPara            ( ) const { return (properties & STYPE_MASK) == STYPE_PARA; }

  inline void setStype          ( const stype_t t )
  {
    assert( t == STYPE_SYMB
	 || t == STYPE_PARA
	 || t == STYPE_LIST
	 || t == STYPE_TERM );
    properties |= t;
  }

  inline void setArity            ( const unsigned a ) { assert( a <= SARITY_N ); properties |= (a << SARITY_SHIFT); }
  //
  // Check if a term node represents a certain symbol
  //
  inline snodeid_t getId            ( ) const { return id; }
  inline unsigned  getArity         ( ) const { return ((properties & SARITY_MASK) >> SARITY_SHIFT); }
  inline char *    getName          ( ) const { assert( isSymb( ) || isPara( ) ); return name; }
  inline Snode *   getCar           ( ) const { return car; }
  inline Snode *   getCdr           ( ) const { return cdr; }
  inline Snode *   get1st           ( ) const;                   // Get first argument in constant time
  inline Snode *   get2nd           ( ) const;                   // Get second argument in constant time
  inline Snode *   get3rd           ( ) const;                   // Get third argument in constant time

  void             print	    ( ostream & ); // Prints the snode

  inline friend ostream &  operator<<( ostream & os, Snode * e )    { assert( e ); e->print( os ); return os; }

  struct idLessThan
  {
    inline bool operator( )( Snode * x, Snode * y )
    {
      return (x->getCar( )->getId( ) <  y->getCar( )->getId( ))
	  || (x->getCar( )->getId( ) == y->getCar( )->getId( ) && x->getCdr( )->getId( ) < y->getCdr( )->getId( ) );
    }
  };

  inline bool hasSortBool        ( ) { assert( isTerm( ) ); Snode * last = getLast( ); return last->hasSymbolId ( SNODE_ID_BOOL ); }
  inline bool hasSortReal        ( ) { assert( isTerm( ) ); Snode * last = getLast( ); return last->hasSymbolId ( SNODE_ID_REAL  ); }
  inline bool hasSortInt         ( ) { assert( isTerm( ) ); Snode * last = getLast( ); return last->hasSymbolId ( SNODE_ID_INT   ); }
  inline bool hasSortArray       ( ) { assert( isTerm( ) ); Snode * last = getLast( ); return last->hasSymbolId ( SNODE_ID_ARRAY ); }
  inline bool hasSortCost        ( ) { assert( isTerm( ) ); Snode * last = getLast( ); return last->hasSymbolId ( SNODE_ID_COST  ); }
  inline bool hasSortUndef       ( ) { assert( isTerm( ) ); Snode * last = getLast( ); return last->hasSymbolId ( SNODE_ID_UNDEF ); }

  inline bool isBool             ( ) { return id == SNODE_ID_BOOL; }
  inline bool isDot              ( ) { return id == SNODE_ID_DOT; }

  inline Snode * getLast ( )
  {
    Snode * l = this; 
    Snode * t = this; 
    t = t->getCdr( );
    while( !t->isSnil( ) )
    {
      l = t->getCar( );
      t = t->getCdr( );
    }

    return l;
  }

  inline string getArgs ( )
  {
    stringstream ss;
    string space = "";
    Snode * l = this->getCdr( );
    while ( !l->isSnil( ) )
    {
      ss << space;
      l->getCar( )->print( ss );
      space = " ";
      l = l->getCdr( );
    }

    return ss.str( );
  }

private:

  inline bool       hasSymbolId    ( const snodeid_t id ) const { assert( isTerm( ) ); return car->getId( ) == id; }

  //
  // Standard informations for terms
  //
  const snodeid_t   id;         // Node unique identifier
  uint32_t          properties; // Contains all the properties of this node (see SnodeTypes.h for bitfields definition)
  Snode *           car;        // For car 
  Snode *           cdr;        // For cdr
  char *            name;       // Name for symbols
};

inline Snode * Snode::get1st ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 0 );
  return getCdr( )->getCar( );
}

inline Snode * Snode::get2nd ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 1 );
  return getCdr( )->getCdr( )->getCar( );
}

inline Snode * Snode::get3rd ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 2 );
  return getCdr( )->getCdr( )->getCdr( )->getCar( );
}

#endif
