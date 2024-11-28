/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen

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

#ifndef SymStore_h
#define SymStore_h

#include "Symbol.h"

#include <common/StringMap.h>

namespace opensmt {
class SymStore {
public:
    SymStore() = default;
    ~SymStore();
    SymStore(SymStore const &) = delete;
    SymStore & operator=(SymStore const &) = delete;
    SymStore(SymStore &&) = default;
    SymStore & operator=(SymStore &&) = default;
    // Constructs a new symbol.

    SymRef newSymb(char const * fname, SRef rsort, vec<SRef> const & args, SymbolConfig const & symConfig) {
        return newSymb(fname, rsort, args, symConfig, false);
    };
    SymRef newSymb(char const * fname, SRef rsort, vec<SRef> const & args) {
        return newSymb(fname, rsort, args, SymConf::Default, false);
    }
    SymRef newInternalSymb(char const * fname, SRef rsort, vec<SRef> const & args, SymbolConfig const & symConfig) {
        return newSymb(fname, rsort, args, symConfig, true);
    }
    bool contains(char const * fname) const { return symbolTable.has(fname); }
    vec<SymRef> const & nameToRef(char const * s) const { return symbolTable[s]; }
    vec<SymRef> & nameToRef(char const * s) { return symbolTable[s]; }

    vec<SymRef> const * getRefOrNull(char const * s) const { return symbolTable.getOrNull(s); }

    Symbol & operator[](SymRef sr) { return ta[sr]; }
    Symbol const & operator[](SymRef tr) const { return ta[tr]; }
    char const * getName(SymRef tr) const { return idToName[ta[tr].getId()]; }

    vec<SymRef> const & getSymbols() const { return symbols; }

    bool isInterpreted(SymRef sr) const { return ta[sr].isInterpreted(); }

#ifdef PEDANTIC_DEBUG
    void compare(SymStore &);
    void check() const;
#endif
private:
    static char const * e_duplicate_symbol;
    // For serialization
    static int const symstore_buf_offs_idx;
    static int const symref_buf_offs_idx;
    static int const symname_buf_offs_idx;

    VecMap<char const *, SymRef, StringHash, Equal<char const *>> symbolTable;
    vec<SymRef> symbols;
    SymbolAllocator ta{1024};
    vec<char *> idToName;

    SymRef newSymb(char const * fname, SRef rsort, vec<SRef> const & args, SymbolConfig const & symConfig,
                   bool subSymb);
};
} // namespace opensmt

#endif
