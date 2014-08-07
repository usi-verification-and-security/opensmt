/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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
