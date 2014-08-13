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

// The Traversal of the node is unnecessary and a result of a confusion
// Code can possibly be reused when define-sort is implemented
char* SStore::buildName(ASTNode& sn)
{
    list<ASTNode*>::iterator it = sn.children->begin();
    char* canon_name;
    asprintf(&canon_name, "%s", (**it).getValue());
    return canon_name;

    asprintf(&canon_name, "%s", (**(it++)).getValue());
    if  (it != sn.children->end()) {
        char* arg_names;
        char* old;
        char* sub_name = buildName(**(it++));
        asprintf(&arg_names, "%s", sub_name);
        free(sub_name);
        for (; it != sn.children->end(); it++) {
            old = arg_names;
            sub_name = buildName(**it);
            asprintf(&arg_names, "%s %s", old, sub_name);
            free(sub_name);
            free(old);
        }
        old = canon_name;
        asprintf(&canon_name, "%s (%s)", old, arg_names);
        free(old);
    }
    return canon_name;
}

SRef SStore::newSort(ASTNode& sn)
{
    SRef sr = SRef_Undef;
    char* canon_name = NULL;
    vec<SRef> tmp;
    IdRef idr = IdRef_Undef;

    if (sn.getType() == CMD_T || sn.getType() == ID_T) {
        list<ASTNode*>::iterator p = sn.children->begin();
        ASTNode& sym_name = **p;
        idr = is.newIdentifier(sym_name);
    } else if (sn.getType() == LID_T) {
        // This is possibly broken
        list<ASTNode*>::iterator it = sn.children->begin();
        for (; it != sn.children->end(); it++) {
            tmp.push(newSort(**it));
        }
    } else assert(false);

    canon_name = buildName(sn);

    if (sortTable.contains(canon_name)) {
        return sortTable[canon_name];
    } else {
        SStrRef nr = ssa.alloc(canon_name);
        sr = sa.alloc(idr, nr, tmp);
        sorts.push(sr);
        sortTable.insert(canon_name, sr);
        return sr;
    }
}

SRef SStore::newSort(IdRef idr, vec<SRef>& rest)
{
    SRef sr = SRef_Undef;
    char* canon_name = NULL;
    char* old;
    if (rest.size() > 0) {
        char* arg_names;
        asprintf(&arg_names, "%s", getName(rest[0]));
        for (int i = 1; i < rest.size(); i++) {
            old = arg_names;
            asprintf(&arg_names, "%s %s", old, getName(rest[i]));
            free(old);
        }
        old = canon_name;
        asprintf(&canon_name, "%s (%s)", is.getName(idr), old);
        free(old);
    } else
        asprintf(&canon_name, "%s", is.getName(idr));

    if (sortTable.contains(canon_name))
        return sortTable[canon_name];
    else {
        SStrRef nr = ssa.alloc(canon_name);
        sr = sa.alloc(idr, nr, rest);
        sorts.push(sr);
        sortTable.insert(canon_name, sr);
        return sr;
    }
}


//void SStore::insertStore(Sort* s) {
//    // temporary hack, finally a finer mem allocation for Sort would be nice?
//    assert(sorts.size() == SRefToSort.size());
//    const char* name = s->getCanonName();
//    SRef sr = sorts.size();
//    sorts.push(sr);
//    sortTable.insert(name, sr);
//    SRefToSort.push(s);
//}

//
// Serialize the sorts
//
void SStore::storeSorts()
{
    for (int i = 0; i < SRefToSort.size(); i++) {
        SRefToSort[i];
    }
}
//void
//SStore::dumpSortsToFile ( ostream & dump_out )
//{
//}
