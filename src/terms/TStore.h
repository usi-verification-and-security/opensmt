#ifndef TSTORE_H
#define TSTORE_H

#include <string>
#include "Term.h"
//#include "Vec.h"
//#include "Map.h"
#include "StringMap.h"

// Contains pairs (TRef p, int i) stating that p is the i-parent of a term
class Occ {
    int i; TRef p;
  public:
    Occ(int i_, TRef p_) : i(i_), p(p_) {}
    Occ() : i(-1), p(TRef_Undef) {};
};



class TStore {
  private:
    VecMap<const char*,TRef,StringHash,Equal<const char*> >  termTable;
    Map<TRef,TId,TRefHash,Equal<TRef> >             trefToId;
    vec<TRef>                                       terms;
    TermAllocator                                   ta;
    vec<vec<Occ> >                                  occList;
    vec<const char*>                                idToName;
  public:
//    Term* insertStore(Term*);
    TRef newTerm(const char* fname, const vec<SRef>& args, bool la = false, bool ra = false, bool ch = false, bool pw = false);
    bool contains(const char* fname)        const { return termTable.contains(fname); }
//    const Term& operator [] (const char* s) const { return ta[termTable[s]]; }
//    Term& operator [] (const char* s)             { return ta[termTable[s]]; }
    const vec<TRef>& nameToRef(const char* s) const { return termTable[s]; }
    vec<TRef>& nameToRef(const char* s)           { return termTable[s]; }
//    Term& operator [] (const char* s)             { return ta[termTable[s]]; }
    Term& operator [] (TRef tr)                          { return ta[tr]; }
    const Term& operator [] (TRef tr)         const { return ta[tr]; }
    void insertOcc(TRef tr, int k_arg, TRef par)         { occList[trefToId[tr]].push(Occ(par, k_arg)); }
    const char* getName(TRef tr)                   const { return idToName[trefToId[tr]]; }
};

#endif
