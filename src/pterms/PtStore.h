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


#ifndef PTSTORE_H
#define PTSTORE_H

#include "Pterm.h"
#include "SymStore.h"

#ifdef PRODUCE_PROOF
#include <unordered_map>
#endif

class SStore; // forward declaration

//struct PTRefHash {
//    uint32_t operator () (const PTRef s) const {
//        return (uint32_t)s; }
//};

class PtermIter {
  private:
    int i;
    vec<PTRef>& idToPTRef;
  public:
    PtermIter(vec<PTRef>& in) : i(0), idToPTRef(in) {}
    PTRef operator* ();/* {
        if (i < idToPTRef.size())
            return idToPTRef[i];
        else
            return PTRef_Undef;
    }*/
    const PtermIter& operator++ ();// { i++; return *this; }
};

class PtStore {
    PtermAllocator pta{1024*1024};
    SymStore&      symstore;
    vec<PTRef>     idToPTRef;

    Map<SymRef,PTRef,SymRefHash,Equal<SymRef> > cterm_map; // Mapping constant symbols to terms
//    vec<SymRef> cterm_keys;

    Map<PTLKey,PTRef,PTLHash,Equal<PTLKey> >    cplx_map;  // Mapping complex terms to canonical terms
//    vec<PTLKey> cplx_keys;

#ifdef PRODUCE_PROOF
    std::unordered_map<SymRef, ipartitions_t, SymRefHash> sym_partitions;
    std::unordered_map<PTRef, ipartitions_t, PTRefHash> term_partitions;
//    Map<SymRef,ipartitions_t*,SymRefHash,Equal<SymRef> > sym_partitions;
//    Map<PTRef,ipartitions_t*,PTRefHash,Equal<PTRef> > term_partitions;
#endif

    Map<PTLKey,PTRef,PTLHash,Equal<PTLKey> >    bool_map;  // Mapping boolean terms to canonical terms
//    vec<PTLKey> bool_keys;
//    friend class Logic;
    static const int ptstore_buf_idx;
    static const int ptstore_vec_idx;
  public:
    PtStore(SymStore& symstore) : symstore(symstore) {}

    PTRef newTerm(const SymRef sym, const vec<PTRef>& ps);/* {
        PTRef tr = pta.alloc(sym, ps); idToPTRef.push(tr);
        assert(idToPTRef.size() == pta.getNumTerms());
        return tr;
    }*/

#ifdef PRODUCE_PROOF
    void assignPartition(unsigned int n, PTRef tr); // The new partition system
    ipartitions_t& getIPartitions(PTRef _t);
    void setIPartitions(PTRef _t, const ipartitions_t& _p);
    void addIPartitions(PTRef _t, const ipartitions_t& _p);
    ipartitions_t& getIPartitions(SymRef _s);
    void setIPartitions(SymRef _s, const ipartitions_t& _p);
    void addIPartitions(SymRef _s, const ipartitions_t& _p);
#endif

    void   free(PTRef r);// { pta.free(r); }  // this is guaranteed to be lazy

    SymRef lookupSymbol(const char* s, const vec<PTRef>& args);

    Pterm& operator[] (PTRef tr);// { return pta[tr]; }
    const Pterm& operator[] (PTRef tr) const;// { return pta[tr]; }

    bool hasCtermKey(SymRef& k);// { return cterm_map.has(k); }
    void addToCtermMap(SymRef& k, PTRef tr);/* {
        cterm_map.insert(k, tr);
//        cterm_keys.push(k);
    }*/
    PTRef getFromCtermMap(SymRef& k);// { return cterm_map[k]; }

    bool hasBoolKey(PTLKey& k);// { return bool_map.has(k); }
    void addToBoolMap(PTLKey& k, PTRef tr);/* {
        bool_map.insert(k, tr);
//        bool_keys.push(k);
    }*/
    PTRef getFromBoolMap(PTLKey& k);// { return bool_map[k]; }

    bool hasCplxKey(PTLKey& k);// { return cplx_map.has(k); }
    void addToCplxMap(PTLKey& k, PTRef tr);/* {
        cplx_map.insert(k, tr);
//        cplx_keys.push(k);
    }*/
    PTRef getFromCplxMap(PTLKey& k);// { return cplx_map[k]; }

    PtermIter getPtermIter();// { return PtermIter(idToPTRef); }
};

#endif
