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


#ifndef ENODESTORE_H
#define ENODESTORE_H

#include "Enode.h"
#include "OsmtInternalException.h"

class Logic;

struct PTRefERefPair { PTRef tr; ERef er; };

class EnodeStore {
    Logic&         logic;
    Map<SigPair,ERef,SigHash,Equal<const SigPair&> > sig_tab;
    EnodeAllocator ea;
    ERef           ERef_Nil;
    ERef           ERef_True;
    ERef           ERef_False;
    ERef           sym_uf_not;
    Map<PTRef,char,PTRefHash,Equal<PTRef> > dist_classes;
    uint32_t       dist_idx;

    Map<PTRef,ERef,PTRefHash,Equal<PTRef> >    termToERef;
    Map<SymRef,ERef,SymRefHash,Equal<SymRef> > symToERef;
    Map<ERef,PTRef,ERefHash,Equal<ERef> >      ERefToTerm;

#ifdef PEDANTIC_DEBUG
    ELAllocator&   fa;
#endif

    vec<PTRef>     index_to_dist;                    // Table distinction index --> proper term
    vec<ERef>      termEnodes;

    ERef  addTerm(ERef sym, ERef args, PTRef pt);
    ERef  addSymb(SymRef t);
    ERef  addList(ERef car, ERef cdr);


public:
    EnodeStore(Logic& l);

    bool needsEnode(PTRef tr) const;
    bool needsRecursiveDefinition(PTRef tr) const;

    const vec<ERef>& getTermEnodes() const { return termEnodes; };

    ERef getEnode_true()  { return ERef_True;  }
    ERef getEnode_false() { return ERef_False; }

    ERef get_Nil() const { return ERef_Nil; }
    void free(ERef er) { ea.free(er); }


    bool         has(PTRef tr)         const { return termToERef.has(tr); }
    ERef         getERef(PTRef tr)     const { return termToERef[tr]; }
    /**
     * Place into er the enode ref of tr if it exists in the store.  Otherwise do not change er.
     * @param tr the pterm ref to look for
     * @param er will contain the enode ref corresponding to tr, or be unchanged
     * @return true if tr is in the store, false if not.
     */
    bool         peekERef(PTRef tr, ERef& er)  const { return termToERef.peek(tr, er); }
    PTRef        getPTRef(ERef er)     const { return ERefToTerm[er]; }

    vec<PTRefERefPair> constructTerm(PTRef tr);

    Enode&       operator[] (ERef e)         { return ea[e]; }
    const Enode& operator[] (ERef e)   const { return ea[e]; }
          Enode& operator[] (PTRef tr)       { return ea[termToERef[tr]]; }
    const Enode& operator[] (PTRef tr) const { return ea[termToERef[tr]]; }

    char getDistIndex(PTRef tr_d) const {
        assert(dist_classes.has(tr_d));
        return dist_classes[tr_d];
    }

    PTRef getDistTerm(dist_t idx) const { return index_to_dist[idx]; }

    void addDistClass(PTRef tr_d) {
        if (dist_classes.has(tr_d)) { return; }
        if (dist_idx >= maxDistinctClasses) {
            throw OsmtInternalException();
        }
        dist_classes.insert(tr_d, dist_idx);
        assert(index_to_dist.size_() == dist_idx);
        index_to_dist.push(tr_d);
        dist_idx++;
    }

    inline bool containsSig(ERef e) const {
        const Enode & en_e = ea[e];
        SigPair sp(ea[ea[en_e.getCar()].getRoot()].getCid(), ea[ea[en_e.getCdr()].getRoot()].getCid());
        return sig_tab.has(sp);
    }

    inline bool containsSig(ERef car, ERef cdr) const {
        SigPair sp(ea[ea[car].getRoot()].getCid(), ea[ea[cdr].getRoot()].getCid());
        return sig_tab.has(sp);
    }


    inline ERef lookupSig(ERef e) const {
        const Enode & en_e = ea[e];
        SigPair sp(ea[ea[en_e.getCar()].getRoot()].getCid(), ea[ea[en_e.getCdr()].getRoot()].getCid());
        return sig_tab[sp];
    }

    inline ERef lookupSig(ERef car, ERef cdr) const {
        SigPair sp(ea[ea[car].getRoot()].getCid(), ea[ea[cdr].getRoot()].getCid());
        return sig_tab[sp];
    }

    inline void removeSig(ERef e) {
        assert(containsSig(e));
        const Enode & en_e = ea[e];
        ERef carRoot = ea[en_e.getCar()].getRoot();
        ERef cdrRoot = ea[en_e.getCdr()].getRoot();
        SigPair sp(ea[carRoot].getCid(), ea[cdrRoot].getCid());
        sig_tab.remove(sp);
        assert(!containsSig(e));
    }

    inline void insertSig(ERef e) {
        const Enode & en_e = ea[e];
        ERef carRoot = ea[en_e.getCar()].getRoot();
        ERef cdrRoot = ea[en_e.getCdr()].getRoot();
        assert(!containsSig(e));
//        assert(e == en_e.getCgPtr()); // MB: Only congruence roots should be inserted
        sig_tab.insert(SigPair(ea[carRoot].getCid(), ea[cdrRoot].getCid()), e);
        assert(containsSig(e));
    }

    ERef addAnonSymb(PTRef tr);

// DEBUG
#ifdef PEDANTIC_DEBUG
    bool checkInvariants();
#endif

    char* printEnode(ERef);

    vec<ERef> getArgTermsAsVector(ERef) const;
//    friend class Egraph;
};

#endif
