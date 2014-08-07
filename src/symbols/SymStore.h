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


#ifndef TSTORE_H
#define TSTORE_H

#include <string>
#include "Symbol.h"
//#include "Vec.h"
//#include "Map.h"
#include "StringMap.h"

// Contains pairs (SymRef p, int i) stating that p is the i-parent of a term
//class Occ {
//    int i; SymRef p;
//  public:
//    Occ(int i_, SymRef p_) : i(i_), p(p_) {}
//    Occ() : i(-1), p(SymRef_Undef) {};
//};



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
