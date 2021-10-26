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

#include <unordered_map>

class Logic;

struct PTRefERefPair { PTRef tr; ERef er; };

class EnodeStore {

    struct Signature {
        std::vector<uint32_t> nums;
    };

    struct SignatureHash {
        std::size_t operator()(Signature const & sig) const {
            auto const & nums = sig.nums;
            std::size_t seed = nums.size();
            for(uint32_t i = 0; i < nums.size(); ++i) {
                seed ^= nums[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
            }
            return seed;
        }
    };

    struct SignatureEqual {
        bool operator()(Signature const & a, Signature const & b) const {
            if (a.nums.size() != b.nums.size()) { return false; }
            for(uint32_t i = 0; i < a.nums.size(); ++i) {
                if (a.nums[i] != b.nums[i]) { return false; }
            }
            return true;
        }
    };

    Logic&         logic;
    EnodeAllocator ea;
    std::unordered_map<Signature, ERef, SignatureHash, SignatureEqual> sig_tab;
    ERef           ERef_True;
    ERef           ERef_False;
    Map<PTRef,char,PTRefHash,Equal<PTRef> > dist_classes;
    uint32_t       dist_idx;

    Map<PTRef,ERef,PTRefHash,Equal<PTRef> >    termToERef;
    Map<ERef,PTRef,ERefHash,Equal<ERef> >      ERefToTerm;

    vec<PTRef>     index_to_dist;                    // Table distinction index --> proper term
    vec<ERef>      termEnodes;

    ERef  addTerm(PTRef pt);
    ERef  addAnonTerm(PTRef pt);

public:
    EnodeStore(Logic& l);

    bool needsEnode(PTRef tr) const;
    bool needsRecursiveDefinition(PTRef tr) const;

    const vec<ERef>& getTermEnodes() const { return termEnodes; };

    ERef getEnode_true()  { return ERef_True;  }
    ERef getEnode_false() { return ERef_False; }

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

    Signature getSignature(ERef e) const {
        Signature ret;
        Enode const & node = ea[e];
        auto size = node.getSize();
        ret.nums.reserve(size + 1);
        ret.nums.push_back(node.getSymbol().x);
        for (uint32_t i = 0; i < size; ++i) {
            ret.nums.push_back(ea[node[i]].getRoot().x);
        }
        return ret;
    }

    inline bool containsSig(ERef e) const {
        return sig_tab.find(getSignature(e)) != sig_tab.end();
    }

    inline ERef lookupSig(ERef e) const {
        assert(containsSig(e));
        return sig_tab.find(getSignature(e))->second;
    }

    inline void removeSig(ERef e) {
        assert(containsSig(e));
        sig_tab.erase(getSignature(e));
        assert(!containsSig(e));
    }

    inline void insertSig(ERef e) {
        assert(!containsSig(e));
        sig_tab.emplace(getSignature(e), e);
        assert(containsSig(e));
    }

    char* printEnode(ERef);

    vec<ERef> getArgTermsAsVector(ERef) const;
};

#endif
