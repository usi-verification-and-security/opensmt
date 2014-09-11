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
#include "SStore.h"

//struct PTRefHash {
//    uint32_t operator () (const PTRef s) const {
//        return (uint32_t)s; }
//};

class PtStore {
#ifndef TERMS_HAVE_EXPLANATIONS
    class Explanation {
      private:
        PtAsgn      reason;
        PTRef       parent;
        PTRef       root;
        int         time_stamp;
      public:
        Explanation()
            : reason(PtAsgn(PTRef_Undef, l_Undef))
            , parent(PTRef_Undef)
            , root(PTRef_Undef)
            , time_stamp(0)
            {}

        void setReason(PtAsgn pta) { reason = pta; }
        void setParent(PTRef p)    { parent = p; }
        void setRoot(PTRef p)      { root = p; }
        void setTimeStamp(int s)   { time_stamp = s; }

        PtAsgn getReason()    const { return reason;     }
        PTRef  getParent()    const { return parent;     }
        PTRef  getRoot()      const { return root;       }
        int    getTimeStamp() const { return time_stamp; }
    };

#endif
    PtermAllocator pta;
    SymStore&      symstore;
    SStore&        sortstore;
    vec<PTRef>     idToPTRef;
#ifndef TERMS_HAVE_EXPLANATIONS
    vec<Explanation> explanations;
#endif
    Map<SymRef,PTRef,SymRefHash,Equal<SymRef> > cterm_map; // Mapping constant symbols to terms
//    vec<SymRef> cterm_keys;

    Map<PTLKey,PTRef,PTLHash,Equal<PTLKey> >    cplx_map;  // Mapping complex terms to canonical terms
//    vec<PTLKey> cplx_keys;

    Map<PTLKey,PTRef,PTLHash,Equal<PTLKey> >    bool_map;  // Mapping boolean terms to canonical terms
//    vec<PTLKey> bool_keys;
//    friend class Logic;
    static const int ptstore_buf_idx;
    static const int ptstore_vec_idx;
  public:
    PtStore(SymStore& symstore_, SStore& sortstore_);

    PTRef  newTerm(const SymRef sym, const vec<PTRef>& ps) {
        PTRef tr = pta.alloc(sym, ps); idToPTRef.push(tr);
        assert(idToPTRef.size() == pta.getNumTerms());
#ifndef TERMS_HAVE_EXPLANATIONS
        explanations.push();
        explanations.last().setRoot(tr);
#endif
        return tr;
    }


    void   free(PTRef r) { pta.free(r); }  // this is guaranteed to be lazy

    SymRef lookupSymbol(const char* s, const vec<PTRef>& args);

    Pterm& operator[] (PTRef tr) { return pta[tr]; }
    const Pterm& operator[] (PTRef tr) const { return pta[tr]; }

#ifndef TERMS_HAVE_EXPLANATIONS
    // Explanation related functions
    void  setReason(PTRef tr, PtAsgn pta) { explanations[operator[](tr).getId()].setReason(pta); }
    void  setParent(PTRef tr, PTRef p)    {
        assert((p == PTRef_Undef) ||
            (symstore[operator[](tr).symb()].rsort() == symstore[operator[](p).symb()].rsort()));
        explanations[operator[](tr).getId()].setParent(p);
    }
    void  setRoot  (PTRef tr, PTRef r)    {
        assert((r == PTRef_Undef) ||
            (symstore[operator[](tr).symb()].rsort() == symstore[operator[](r).symb()].rsort()));
        explanations[operator[](tr).getId()].setRoot(r); }
    void  setTimeStamp(PTRef tr, int s)   { explanations[operator[](tr).getId()].setTimeStamp(s); }

    PtAsgn getReason(PTRef tr)    const { return explanations[operator[](tr).getId()].getReason(); }
    PTRef  getParent(PTRef tr)    const { return explanations[operator[](tr).getId()].getParent(); }
    PTRef  getRoot(PTRef tr)      const { return explanations[operator[](tr).getId()].getRoot(); }
    int    getTimeStamp(PTRef tr) const { return explanations[operator[](tr).getId()].getTimeStamp(); }
#endif
    char* printTerm(PTRef, bool ext = false) const;
    char* printTerm_(PTRef, bool ext = false) const;

    bool hasCtermKey(SymRef& k) { return cterm_map.contains(k); }
    void addToCtermMap(SymRef& k, PTRef tr) {
        cterm_map.insert(k, tr);
//        cterm_keys.push(k);
    }
    PTRef getFromCtermMap(SymRef& k) { return cterm_map[k]; }

    bool hasBoolKey(PTLKey& k) { return bool_map.contains(k); }
    void addToBoolMap(PTLKey& k, PTRef tr) {
        bool_map.insert(k, tr);
//        bool_keys.push(k);
    }
    PTRef getFromBoolMap(PTLKey& k) { return bool_map[k]; }

    bool hasCplxKey(PTLKey& k) { return cplx_map.contains(k); }
    void addToCplxMap(PTLKey& k, PTRef tr) {
        cplx_map.insert(k, tr);
//        cplx_keys.push(k);
    }
    PTRef getFromCplxMap(PTLKey& k) { return cplx_map[k]; }

    int* serializeTerms() const;
    void deserializeTerms(const int*);
};

#endif
