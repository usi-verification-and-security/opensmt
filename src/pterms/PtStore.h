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
    Map<PTLKey,PTRef,PTLHash,Equal<PTLKey> >    bool_map;  // Mapping boolean terms to canonical terms
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
