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
#include "OsmtApiException.h"

const char* SymStore::e_duplicate_symbol = "Symbol Store: symbol already exists";
const int   SymStore::symstore_buf_offs_idx = 1;
const int   SymStore::symref_buf_offs_idx   = 2;
const int   SymStore::symname_buf_offs_idx  = 3;

SymStore::~SymStore() {
    for (int i = 0; i < idToName.size(); i++)
        free(idToName[i]);
}

SymRef SymStore::newSymb(const char * fname, SRef rsort, vec<SRef> const & args, SymbolConfig const & symConfig) {
    // Check if there already is a term called fname with same number of arguments of the same sort
    auto* symrefs = getRefOrNull(fname);

    if (symrefs) {
        const vec<SymRef>& trs = *symrefs;
        for (SymRef symref : trs) {
            auto const & symbol = ta[symref];
            if (symbol.rsort() == rsort and symbol.nargs() == args.size_()
                    and symbol.commutes() == symConfig.commutes
                    and symbol.noScoping() == symConfig.noScoping
                    and symbol.isInterpreted() == symConfig.isInterpreted) {
                if (std::equal(symbol.begin(), symbol.end(), args.begin())) {
                    return symref;
                }
            }
        }
        if (!symConfig.isInterpreted) {
          // Only builtin functions like "=" or "+" should be polymorphic
          throw OsmtApiException("Symbol `" + std::string(fname) + "` has conflicting definitions");
        }
    }

    bool newsym = (symrefs == nullptr);
    SymRef tr = ta.alloc(rsort, args, symConfig);
    SymId id = symbols.size();
    symbols.push(tr);

    char* tmp_name = strdup(fname);
    idToName.push(tmp_name);            // Map the id to name, used in error reporting
    ta[tr].id = id;                     // Tell the term its id, used in error reporting, and checking whether two terms could be equal in future?
    if (newsym) {
        vec<SymRef> trs;
        trs.push(tr);
        symbolTable.insert(tmp_name, trs);
    }
    else {
        symbolTable[tmp_name].push(tr);           // Map the name to term reference (why not id?), used in parsing
    }
    return tr;
}

#ifdef PEDANTIC_DEBUG
void SymStore::compare(SymStore& other)
{
    if (symbols.size() != other.symbols.size()) assert(false);
    for (int i = 0; i < symbols.size(); i++) {
        if (symbols[i] != other.symbols[i]) assert(false);
        Symbol& my_sym = ta[symbols[i]];
        Symbol& other_sym = other.ta[symbols[i]];
        my_sym.compare(other_sym);
    }
    for (int i = 0; i < idToName.size(); i++) {
        assert(strcmp(other.idToName[i], idToName[i]) == 0);
        vec<SymRef>& my_v = symbolTable[idToName[i]];
        vec<SymRef>& other_v = other.symbolTable[idToName[i]];
        assert(my_v.size() == other_v.size());
        for (int j = 0; j < my_v.size(); j++)
            assert(my_v[j] == other_v[j]);
    }
}

void SymStore::check() const
{
    for (int i = 0; i < symbols.size(); i++)
        assert(operator[] (symbols[i]).id == i);
}
#endif

