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
#include "StringMap.h"

class SymStore {
  private:
    VecMap<const char*,SymRef,StringHash,Equal<const char*> >  symbolTable;
    vec<SymRef>                                 symbols;
    SymbolAllocator                             ta{1024};
  public:
    vec<char*>                                  idToName;

    ~SymStore();
    // Construct a new symbol.  The first argument in args is the return
    // sort of the symbol
    SymRef newSymb(const char *fname, vec<SRef> const & args, SymbolConfig const & symConfig);
    SymRef newSymb(const char *fname, vec<SRef> const & args) { return newSymb(fname, args, SymConf::Default); }
    bool contains(const char* fname)            const { return symbolTable.has(fname); }
    const vec<SymRef>& nameToRef(const char* s) const { return symbolTable[s]; }
    vec<SymRef>& nameToRef(const char* s)             { return symbolTable[s]; }

    // Replace with std::optional if C++17 will be required
    const vec<SymRef>* getRefOrNull(const char* s) const { return symbolTable.getOrNull(s); }

    Symbol& operator [] (SymRef sr)                   { return ta[sr]; }
    const Symbol& operator [] (SymRef tr)       const { return ta[tr]; }
    const char* getName(SymRef tr)              const { return idToName[ta[tr].getId()]; }

    const vec<SymRef>& getSymbols()             const { return symbols; }

    bool isInterpreted(SymRef sr)               const { return ta[sr].isInterpreted(); }

#ifdef PEDANTIC_DEBUG
    void compare(SymStore&);
    void check() const;
#endif
private:
    static const char* e_duplicate_symbol;
    // For serialization
    static const int symstore_buf_offs_idx;
    static const int symref_buf_offs_idx;
    static const int symname_buf_offs_idx;
};

#endif
