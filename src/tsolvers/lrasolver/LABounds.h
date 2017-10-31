#ifndef LABOUNDS_H
#define LABOUNDS_H

#include "Delta.h"
#include "LARefs.h"
#include "LAVar.h"
#include "Pterm.h"


class LABound
{
    struct {
        unsigned type    : 1;  // Upper / lower
        unsigned reverse : 1;  // is this used?
        unsigned active  : 1;  // is this used?
        unsigned idx     : 29; // The index in variable's bound list
    };
    Delta delta;
    PtAsgn leq_pta;
public:
    LABound(BoundT type, PtAsgn leq_pta, const Delta& delta)
        : type(type.t), reverse(false), active(true), idx(536870911), leq_pta(leq_pta), delta(delta)
    {}
    void setIdx(int i)  { idx = i; }
    int  getIdx() const { return idx; }
    const Delta& getValue() const { return delta; }
    BoundT getType() const { return { type }; }
    PTRef getPTRef() const { return leq_pta.tr;  }
};

class LABoundAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_bounds;
    static int laboundWord32Size() {
        return (sizeof(LABound)) / sizeof(uint32_t); }
public:
    LABoundAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_bounds(0) {}
    LABoundAllocator() : n_bounds(0) {}
    unsigned getNumBounds() const { return n_bounds; }

    LABoundRef alloc(BoundT type, PtAsgn leq_pta, const Delta& delta)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
        LABoundRef id = {v};
        new (lea(id)) LABound(type, leq_pta, delta);
        return id;
    }
    LABound&       operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LABound& operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    LABound*       lea       (LABoundRef r)       { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
    const LABound* lea       (LABoundRef r) const { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
    LABoundRef     ael       (const LABound* t)   { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundRef rf; rf.x = r; return rf; }
    void printBound(const LABoundRef r) const { }
    void clear() {}
};

class LABoundList
{
    friend class LABoundListAllocator;
    friend class LABoundStore; // Needed so that I can sort the bounds in the list
    struct {
        unsigned reloc   : 1;
        unsigned sz      : 31;
    };
    LVRef          v; // Do we need this?
    LABoundListRef reloc_target;
    LABoundRef     bounds[0];
public:
    bool           reloced   ()                 const { return reloc; }
    LABoundListRef relocation()                 const { return reloc_target; }
    void           relocate  (LABoundListRef r)       { reloc = 1; reloc_target = r; }
    unsigned       size      ()                 const { return sz; }
    LABoundRef     operator[](int i)            const { return bounds[i]; }
    LVRef          getVar()                     const { return v; }
    LABoundList(LVRef v, const vec<LABoundRef>& bs) : v(v), reloc(0), sz(bs.size()) {
        for (int i = 0; i < bs.size(); i++) bounds[i] = bs[i];
    }
};

class bound_lessthan {
    LABoundAllocator& ba;
public:
    bound_lessthan(LABoundAllocator& ba) : ba(ba) {}
    bool operator() (LABoundRef r1, LABoundRef r2) const { return ba[r1].getValue() < ba[r2].getValue(); }
};

class LABoundListAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_boundlists;
    static int boundlistWord32Size(int size) {
        return (sizeof(LABoundList) + (sizeof(LABoundRef)*size)) / sizeof(uint32_t); }
public:
    LABoundListAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_boundlists(0) {}
    LABoundListAllocator() : n_boundlists(0) {}

    void moveTo(LABoundListAllocator& to) {
        to.n_boundlists = n_boundlists;
        RegionAllocator<uint32_t>::moveTo(to);
    }

    LABoundListRef alloc(const LVRef v, const vec<LABoundRef>& bs)
    {
        uint32_t b = RegionAllocator<uint32_t>::alloc(boundlistWord32Size(bs.size()));
        LABoundListRef id = {b};
        new (lea(id)) LABoundList(v, bs);
        return id;
    }
    LABoundListRef     alloc(LABoundList& from) {
        vec<LABoundRef> tmp;
        for (int i = 0; i < from.size(); i++)
            tmp.push(from[i]);
        return alloc(from.getVar(), tmp);
    }
    LABoundList&       operator[](LABoundListRef r)       { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LABoundList& operator[](LABoundListRef r) const { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
    LABoundList*       lea(LABoundListRef r)              { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
    const LABoundList* lea(LABoundListRef r) const        { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
    LABoundListRef     ael(const LABoundList* t)          { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundListRef rf; rf.x = r; return rf; }

    void free(LABoundListRef tid)
    {
        LABoundList& b = operator[](tid);
        RegionAllocator<uint32_t>::free(boundlistWord32Size(b.size()));
    }
    void reloc(LABoundListRef& tr, LABoundListAllocator& to)
    {
        LABoundList& bl = operator[](tr);
        if (bl.reloced()) { tr = bl.relocation(); return; }
        tr = to.alloc(bl);
        bl.relocate(tr);
        to[tr].sz = bl.size();
        to[tr].v  = bl.getVar();
    }
};

struct LABoundRefPair { LABoundRef pos; LABoundRef neg; };

class LABoundStore
{
    struct BoundInfo { LVRef v; LABoundRef b1; LABoundRef b2; PTId leq_id; };
    struct LABoundRefPair { LABoundRef lo; LABoundRef hi; };
    vec<BoundInfo> in_bounds;
    LABoundAllocator& ba;
    LABoundListAllocator& bla;
    LAVarAllocator& lva;
    vec<LABoundRefPair> ptermToLABoundsRef;

public:
    LABoundStore(LABoundAllocator& ba, LABoundListAllocator& bla, LAVarAllocator& lva);
    void addBound(LVRef v, PTRef leq_tr, PTId leq_id, const Real& constr, BoundT bound_t);
    void buildBounds(vec<LABoundRefPair>& ptermToLABoundRef);
    LABoundRef getLowerBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].lbound()]; }
    LABoundRef getUpperBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].ubound()]; }
};


void
LABoundStore::addBound(LVRef v, PTRef leq_ref, PTId leq_id, const Real& constr, BoundT bound_t)
{
    LABoundRef br_pos = ba.alloc(bound_t, PtAsgn(leq_ref, l_True), Delta(constr));
    LABoundRef br_neg;

    if (bound_t == bound_u)
        br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), Delta(constr, 1));
    else
        br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), Delta(constr, -1));

    in_bounds.push(BoundInfo{v, br_pos, br_neg, leq_id});
}


void LABoundStore::buildBounds(vec<LABoundRefPair>& ptermToLABoundRefs)
{
    VecMap<LVRef, BoundInfo, LVRefHash> bounds_map;

    for (int i = 0; i < in_bounds.size(); i++) {
        LVRef v = in_bounds[i].v;
        if (!bounds_map.has(v))
            bounds_map.insert(v, vec<BoundInfo>());
        bounds_map[v].push(in_bounds[i]);
        while (ptermToLABoundsRef.size() <= in_bounds[i].leq_id)
            ptermToLABoundsRef.push({ LABoundRef_Undef, LABoundRef_Undef });
        ptermToLABoundsRef[in_bounds[i].leq_id] = { in_bounds[i].b1, in_bounds[i].b2 };
    }
    vec<LVRef> keys;
    bounds_map.getKeys(keys);
    for (int i = 0; i < keys.size(); i++) {
        vec<LABoundRef> refs;
        for (int j = 0; j < bounds_map[keys[i]].size(); i++) {
            BoundInfo &info = bounds_map[keys[i]][j];
            refs.push(info.b1);
            refs.push(info.b2);
        }
        LABoundListRef br = bla.alloc(keys[i], refs);
        sort<LABoundRef,bound_lessthan>(bla[br].bounds, bla[br].size(), bound_lessthan(ba));
        for (int j = 0; j < bla[br].size(); j++)
            ba[bla[br][j]].setIdx(j);
    }
}

#endif
