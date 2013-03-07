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
    Map<SymRef,SymId,SymRefHash,Equal<SymRef> >             symrefToId;
    vec<SymRef>                                       symbols;
    SymbolAllocator                                   ta;
//    vec<vec<Occ> >                                  occList;
    vec<const char*>                                idToName;
  public:
    SymRef newSymb(const char* fname, const vec<SRef>& args, bool la = false, bool ra = false, bool ch = false, bool pw = false);
    bool contains(const char* fname)            const { return symbolTable.contains(fname); }
    const vec<SymRef>& nameToRef(const char* s) const { return symbolTable[s]; }
    vec<SymRef>& nameToRef(const char* s)             { return symbolTable[s]; }

    Symbol& operator [] (SymRef sr)                   { return ta[sr]; }
    const Symbol& operator [] (SymRef tr)       const { return ta[tr]; }
//    void insertOcc(SymRef tr, int k_arg, SymRef par)  { occList[symrefToId[tr]].push(Occ(par, k_arg)); }
    const char* getName(SymRef tr)              const { return idToName[symrefToId[tr]]; }
};

#endif
