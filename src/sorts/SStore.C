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

gSymbol::gSymbol( char* n, int ar, char* attr )
    : name(n)
    , arity(ar)
    , attrib(attr)
{
    stringstream ss;
    ss << name << ", " << arity;
    canon_name = strdup(ss.str().c_str());
}

gSymbol::gSymbol(ASTNode& n)
{
    list<ASTNode*>::iterator it = n.children->begin();
    name = strdup((**it).getValue());
    it++;
    arity = atoi((**it).getValue());
    stringstream ss;
    ss << name << ", " << arity;
    canon_name = strdup(ss.str().c_str());
}

const char* gSymbol::getCanonName() const
{
    return canon_name;
}

void SStore::initializeStore( )
{
}

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
}
