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

const char* SymStore::e_duplicate_symbol = "Symbol Store: symbol already exists";
const int   SymStore::symstore_buf_offs_idx = 1;
const int   SymStore::symref_buf_offs_idx   = 2;
const int   SymStore::symname_buf_offs_idx  = 3;

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

int* SymStore::serializeSymbols()
{
    int* buf = NULL;

    // Compute the sizes
    assert(sizeof(SymRef) == sizeof(int));
    int symref_buf_sz = symbols.size() + 1;
    int* symstore_buf = ta.serialize();
    int symstore_buf_sz = symstore_buf[0];

    // Get the total size required to store the symbol names
    int symname_buf_sz = sizeof(int); // Contains always the size
    for (int i = 0; i < idToName.size(); i++)
        symname_buf_sz += strlen(idToName[i]) + 1;

    int symstore_buf_offs = 4;
    int symref_buf_offs = symstore_buf_offs+symstore_buf_sz;
    int symname_buf_offs = symref_buf_offs+symref_buf_sz;

    int buf_sz = (symstore_buf_sz + symref_buf_sz + 4)*sizeof(int) + symname_buf_sz
        + (symname_buf_sz % sizeof(int) == 0 ? 0 : 4-symname_buf_sz % sizeof(int));
    assert(buf_sz % sizeof(int) == 0);
    buf = (int*) malloc(buf_sz);
    buf[0] = buf_sz / sizeof(int) + (buf_sz % sizeof(int) == 0 ? 0 : 1);
    buf[symstore_buf_offs_idx] = symstore_buf_offs;
    buf[symref_buf_offs_idx] = symref_buf_offs;
    buf[symname_buf_offs_idx] = symname_buf_offs;


    // Copy symstore
    int* symstore_buf_entailed = &buf[symstore_buf_offs];
    for (int i = 0; i < symstore_buf_sz; i++)
        symstore_buf_entailed[i] = symstore_buf[i];
    free(symstore_buf);

    // Copy symrefs
    int* symref_buf = &buf[symref_buf_offs];
    symref_buf[0] = symref_buf_sz;
#ifdef PEDANTIC_DEBUG
    cerr << "Storing " << symref_buf_sz << " symrefs" << endl;
#endif
    for (int i = 0; i < symbols.size(); i++)
        symref_buf[i+1] = symbols[i].x;

    // Copy symnames (in id order)
    buf[symname_buf_offs] = symname_buf_sz;
    char* symname_buf = (char*)&buf[symname_buf_offs + 1];
    int p = 0;
    for (int i = 0; i < idToName.size(); i++) {
        strcpy(&symname_buf[p], idToName[i]);
        p += strlen(idToName[i])+1;
    }
#ifdef PEDANTIC_DEBUG
    cerr << "Stored the SymStore" << endl;
    cerr << " - " << buf[buf[symstore_buf_offs_idx]] << " words for symbols" << endl;
    cerr << " - " << buf[buf[symref_buf_offs_idx]] << " symrefs" << endl;
    cerr << " - " << buf[buf[symname_buf_offs_idx]] << " chars for symnames" << endl;
#endif
    return buf;
}

void SymStore::deserializeSymbols(int* buf)
{
#ifdef PEDANTIC_DEBUG
    cerr << "SymStore deserializeSymbols got " << buf[0] << " words of data" << endl;
#endif
    int symstore_buf_offs = buf[symstore_buf_offs_idx];
    int* symstore_buf = &buf[symstore_buf_offs];
    int symref_buf_offs = buf[symref_buf_offs_idx];
    int* symref_buf = &buf[symref_buf_offs];
    int symname_buf_offs = buf[symname_buf_offs_idx];
    int* symname_buf = &buf[symname_buf_offs];
#ifdef PEDANTIC_DEBUG
    cerr << "Reading " << buf[symstore_buf_offs] << " words for symbols" << endl;
#endif
    ta.deserialize(symstore_buf);
    uint32_t symref_buf_sz = symref_buf[0];
#ifdef PEDANTIC_DEBUG
    cerr << "Reading " << symref_buf_sz << " words for symrefs" << endl;
#endif
    for (uint32_t i = 0; i < symref_buf_sz-1; i++) {
        SymRef sr = SymRef({(uint32_t)symref_buf[i+1]});
        if (i < symbols.size_())
            assert(symbols[i] == sr);
        else
            symbols.push(sr);
        assert(ta[sr].id == i);
    }

    int symname_buf_sz = symname_buf[0];
#ifdef PEDANTIC_DEBUG
    cerr << "Reading " << symname_buf_sz << " characters for symnames" << endl;
#endif
    char* symname_buf_proper = (char*)&symname_buf[1];
    for (int p = 0, sym_id = 0; p < symname_buf_sz-4; sym_id++) {
        int name_sz = strlen(&symname_buf_proper[p]);
#ifdef PEDANTIC_DEBUG
        cerr << "  string at " << p << " is " << &symname_buf_proper[p] << endl;
#endif
        if (sym_id < idToName.size())
            assert(strcmp(idToName[sym_id], &symname_buf_proper[p]) == 0);
        else {
            char* name_out;
            asprintf(&name_out, "%s", &symname_buf_proper[p]);
            idToName.push(name_out);
            cerr << "Added new symbol " << name_out << endl;
            if (symbolTable.contains(name_out)) {
                vec<SymRef>& symrefs = symbolTable[name_out];
                bool found = false;
                for (int j = 0; j < symrefs.size(); j++) {
                    if (symrefs[j] == symbols[sym_id]) {
                        found = true; break; }
                }
                if (!found) {
#ifdef PEDANTIC_DEBUG
                    cerr << "mapping symbol name " << name_out << " to SymRef " << symbols[sym_id].x << endl;
#endif
                    symrefs.push(symbols[sym_id]);
                }
            }
            else {
                vec<SymRef> tmp;
                tmp.push(symbols[sym_id]);
                symbolTable.insert(name_out, tmp);
#ifdef PEDANTIC_DEBUG
                cerr << "mapping symbol name " << name_out << " to SymRef " << symbols[sym_id].x << endl;
#endif
            }
        }
        p += name_sz+1;
    }
}
