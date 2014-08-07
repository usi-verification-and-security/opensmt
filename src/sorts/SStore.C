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
