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

#include "SStore.h"

Symbol::Symbol( char* n, int ar, char* attr )
    : name(n)
    , arity(ar)
    , attrib(attr)
{
    stringstream ss;
    ss << name << ", " << arity;
    canon_name = strdup(ss.str().c_str());
}

Symbol::Symbol(ASTNode& n)
{
    list<ASTNode*>::iterator it = n.children->begin();
    name = strdup((**it).getValue());
    it++;
    arity = atoi((**it).getValue());
    stringstream ss;
    ss << name << ", " << arity;
    canon_name = strdup(ss.str().c_str());
}

const char* Symbol::getCanonName() const
{
    return canon_name;
}

void SStore::initializeStore( )
{
}

//
// Inserts a symbol
//
//void SStore::insertSymbol( Identifier* i, int arity, string* attrib )
//{
//  assert( i );
  // Consistency for id
//  assert( (snodeid_t)id_to_snode.size( ) == s->getId( ) );
  // Symbol is not there
//  assert( name_to_symbol.find( s->getCanonName( ) ) == name_to_symbol.end( ) );
  // Insert Symbol
//  Symbol* s = new Symbol(*(i->toString()), arity, *(attrib));
//  name_to_symbol.insert(*(s->getCanonName()), s);
//  id_to_snode.push_back( s );
//}

//void SStore::insertSymbol( Symbol& s_in)
//{
//    Symbol* s = new Symbol(s_in);
//    name_to_symbol.insert(*(s->getCanonName()), s);
//
//    id_to_snode.push_back( s );
//}

//
// Retrieves a symbol from the name
//
//Symbol* SStore::lookupSymbol( const string* name )
//{
//  assert( name );
//  Symbol* s;
//  if (name_to_symbol.peek(*name, s))
//    return s;
//  else
//    return NULL;
//}

//
// SStore::insertStore
// Arguments: Sort* s
// Returns: Sort*
// Description: Insert a sort reference s into Store.
// preconditions: store does not contain name
//
void SStore::insertStore(Sort* s) {
    // temporary hack, finally a finer mem allocation for Sort would be nice?
    assert(sorts.size() == SRefToSort.size());
    const char* name = s->getCanonName();
    SRef sr = sorts.size();
    sorts.push(sr);
    sortTable.insert(name, sr);
    SRefToSort.push(s);
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
