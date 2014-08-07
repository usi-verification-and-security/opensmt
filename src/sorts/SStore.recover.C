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

#include "SStore.h"

Symbol::Symbol( string& n, int ar, string& attr )
    : name(n)
    , arity(ar)
    , attrib(attr)
{
    stringstream ss;
    ss << name << ", " << arity;
    canon_name = string(ss.str());
}

Symbol::Symbol(ASTNode& n)
{
    list<ASTNode*>::iterator it = n.children->begin();
    name = string((**it).getValue());
    it++;
    arity = atoi((**it).getValue());
    stringstream ss;
    ss << name << ", " << arity;
    canon_name = string(ss.str());
}

const string* Symbol::getCanonName() const
{
    return &canon_name;
}

void SStore::initializeStore( )
{
}

//
// Inserts a symbol
//
void SStore::insertSymbol( Identifier* i, int arity, string* attrib )
{
  assert( i );
  // Consistency for id
//  assert( (snodeid_t)id_to_snode.size( ) == s->getId( ) );
  // Symbol is not there
//  assert( name_to_symbol.find( s->getCanonName( ) ) == name_to_symbol.end( ) );
  // Insert Symbol
  Symbol* s = new Symbol(*(i->toString()), arity, *(attrib));
  name_to_symbol.insert(*(s->getCanonName()), s);
  id_to_snode.push_back( s );
}

void SStore::insertSymbol( Symbol& s_in)
{
    Symbol* s = new Symbol(s_in);
    name_to_symbol.insert(*(s->getCanonName()), s);

    id_to_snode.push_back( s );
}

//
// Retrieves a symbol from the name
//
Symbol* SStore::lookupSymbol( const string* name )
{
  assert( name );
  Symbol* s;
  if (name_to_symbol.peek(*name, s))
    return s;
  else
    return NULL;
}

//
// SStore::insertStore
// Arguments: Sort* s
// Returns: Sort*
// Description: Insert a sort s into Store if it not already there.  Returns a pointer
// to the inserted sort.
//
Sort* SStore::insertStore( Sort* s )
{
  Sort * x = store.insert( s );
  return x;
}


void
SStore::dumpSortsToFile ( ostream & dump_out )
{
/*
  // Dump function declarations
  for ( map< const string*, Symbol * >::iterator it = name_to_symbol.begin( )
      ; it != name_to_symbol.end( )
      ; it ++ )
  {
    Symbol* s = it->second;
    // Skip predefined symbols
    if ( s->isPredef() )
      continue;
    dump_out << "(declare-sort " << s << " 0)" << endl;
  }
*/
}
