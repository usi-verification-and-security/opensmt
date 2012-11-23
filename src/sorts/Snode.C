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

#include "Snode.h"

//
// Constructor for ENIL
//
Snode::Snode( )
  : id         ( SNODE_ID_SNIL )
  , properties ( 0 )
  , car        ( NULL )
  , cdr        ( NULL )
  , name       ( NULL )
{ 
  setStype( STYPE_LIST );
}
//
// Constructor for new Symbols/Parameters
//
Snode::Snode( const snodeid_t id_
	    , const char *    name_ 
	    , const bool      para
	    )
  : id         ( id_ )
  , properties ( 0 )
  , car        ( NULL )
  , cdr        ( NULL )
  , name       ( NULL )
{
  if ( para )
    setStype( STYPE_PARA );
  else
    setStype( STYPE_SYMB );
  name = new char[ strlen( name_ ) + 1 ];
  strcpy( name, name_ );
}
//
// Constructor for new Terms/Lists
//
Snode::Snode( const snodeid_t id_
            , Snode *         car_
            , Snode *         cdr_ )
  : id         ( id_ )
  , properties ( 0 )
  , car        ( car_ )
  , cdr        ( cdr_ )
  , name       ( NULL )
{
  assert( car );
  assert( cdr );
  assert( car->isTerm( ) || car->isSymb( ) || car->isPara( ) );
  assert( cdr->isList( ) );
  //
  // If car is term, then this node is a list
  //
  if ( car->isTerm( ) )
  {
    setStype( STYPE_LIST );
    if ( cdr->getArity( ) == SMAX_ARITY - 1 )
      setArity( cdr->getArity( ) );
    else
      setArity( cdr->getArity( ) + 1 );
  }
  //
  // Otherwise this node is a term
  //
  else
  {
    //
    // Set Stype and arity
    //
    setStype( STYPE_TERM );
    if ( cdr->isSnil( ) )
      setArity( cdr->getArity( ) + 1 );
    else
      setArity( cdr->getArity( ) );
  }

  assert( isTerm( ) || isList( ) );
}

Snode::~Snode ( )
{
  if ( name ) delete [] name;
}

void Snode::print( ostream & os )
{
  Snode * p = NULL;
  assert( !isDot( ) );

  if( isSymb( ) || isPara( ) )
    os << getName( );
  else if ( isTerm( ) )
  {
    const int arity = getArity( );
    string space;
    // Print Arguments
    if ( car->isDot( ) )
    {
      os << "(";
      p = cdr;
      for ( int i = 0 ; i < arity ; i ++ )
      {
        assert( !p->isSnil( ) );
        os << space;
	p->car->print( os );
        p = p->cdr;
        space = " ";
      }
      os << ")";
    }
    else
    {
      car->print( os );
    }
  }
  else if ( isList( ) )
  {
    if ( isSnil( ) )
      os << "-";
    else
    {
      os << "[";
      car->print( os );

      p = cdr;
      while ( !p->isSnil( ) )
      {
	os << ", ";
	p->car->print( os );
	p = p->cdr;
      }

      os << "]";
    }
  }
  else if ( isSnil( ) )
  {
    os << "-";
  }
  else
  {
    opensmt_error( "unknown case value" );
  }
}
