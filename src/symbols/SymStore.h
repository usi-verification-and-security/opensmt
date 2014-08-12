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


#ifndef SymStore_h
#define SymStore_h

#include <string>
#include "Symbol.h"
#include "StringMap.h"

class SymStore {
  private:
    VecMap<const char*,SymRef,StringHash,Equal<const char*> >  symbolTable;
    Map<SymRef,SymId,SymRefHash,Equal<SymRef> > symrefToId;
    vec<SymRef>                                 symbols;
    SymbolAllocator                             ta;
    vec<char*>                                  idToName;
  public:
    ~SymStore();
    // Construct a new symbol.  The first argument in args is the return
    // sort of the symbol
    SymRef newSymb(const char* fname, const vec<SRef>& args, const char** msg, bool la = false, bool ra = false, bool ch = false, bool pw = false);
    bool contains(const char* fname)            const { return symbolTable.contains(fname); }
    bool contains(SymRef sr)                    const { return symrefToId.contains(sr); }
    const vec<SymRef>& nameToRef(const char* s) const { return symbolTable[s]; }
    vec<SymRef>& nameToRef(const char* s)             { return symbolTable[s]; }

    Symbol& operator [] (SymRef sr)                   { return ta[sr]; }
    const Symbol& operator [] (SymRef tr)       const { return ta[tr]; }
//    void insertOcc(SymRef tr, int k_arg, SymRef par)  { occList[symrefToId[tr]].push(Occ(par, k_arg)); }
    const char* getName(SymRef tr)              const { return idToName[symrefToId[tr]]; }
private:
    const char* e_duplicate_symbol;
};

#endif
