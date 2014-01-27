#ifndef PTSTORE_H
#define PTSTORE_H

#include "Pterm.h"
#include "SymStore.h"
#include "SStore.h"

//struct PTRefHash {
//    uint32_t operator () (const PTRef s) const {
//        return (uint32_t)s; }
//};



class PtStore {
    PtermAllocator pta;
    SymStore&      symstore;
    SStore&        sortstore;

    Map<SymRef,PTRef,SymRefHash,Equal<SymRef> > cterm_map; // Mapping constant symbols to terms
    Map<PTLKey,PTRef,PTLHash,Equal<PTLKey> >    cplx_map;  // Mapping complex terms to canonical terms
    friend class Logic;
  public:
    PtStore(SymStore& symstore_, SStore& sortstore_);

    PTRef  newTerm(const SymRef sym, const vec<PTRef>& ps) { return pta.alloc(sym, ps); }

    void   free(PTRef r) { pta.free(r); }  // this is guaranteed to be lazy

    SymRef lookupSymbol(const char* s, const vec<PTRef>& args);

    Pterm& operator[] (PTRef tr) { return pta[tr]; }
    const Pterm& operator[] (PTRef tr) const { return pta[tr]; }

    char* printTerm(PTRef, bool ext = false) const;
    char* printTerm_(PTRef, bool ext = false) const;
};

#endif
