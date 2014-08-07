/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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

