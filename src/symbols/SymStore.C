/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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


#include "string.h"
#include "SymStore.h"
#include "Symbol.h"

static const char* e_duplicate_symbol = "Symbol Store: symbol already exists";

SymStore::~SymStore() {
    for (int i = 0; i < idToName.size(); i++)
        free(idToName[i]);
}

SymRef SymStore::newSymb(const char* fname, const vec<SRef>& args, const char** msg, bool, bool, bool, bool) {
    // Check if there already is a term called fname with same number of arguments of the same sort
    bool newsym = !contains(fname);
    if (newsym == false) {
        const vec<SymRef>& trs = symbolTable[fname];
        for (int i = 0; i < trs.size(); i++) {
            if (ta[trs[i]].rsort() == args[0] && ta[trs[i]].nargs() == args.size_()-1) {
                uint32_t j;
                for (j = 0; j < ta[trs[i]].nargs(); j++) {
                    if (ta[trs[i]][j] != args[j+1])
                        break;
                }
                if (j == ta[trs[i]].nargs()) { // The term exists already
                    *msg = e_duplicate_symbol;
                    return SymRef_Undef;
                }
            }
        }
    }

    SymRef tr = ta.alloc(args, false);
    SymId id = symbols.size();
    symbols.push(tr);

    symrefToId.insert(tr, id);
//    occList.push();                     // Get the occurrence list for this term
    if (newsym) {
        vec<SymRef> trs;
        symbolTable.insert(fname, trs);
    }
    symbolTable[fname].push(tr);           // Map the name to term reference (why not id?), used in parsing
    char* tmp_name = strdup(fname);
    idToName.push(tmp_name);            // Map the id to name, used in error reporting
    ta[tr].id = id;                     // Tell the term its id, used in error reporting, and checking whether two terms could be equal in future?
    return tr;
}

