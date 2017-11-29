#ifndef LABOUNDS_H
#define LABOUNDS_H

#include "Delta.h"
#include "LARefs.h"
#include "LAVar.h"
#include "Pterm.h"


class LABound
{
    char type;    // Upper / lower
    char reverse; // is this used?
    char active;  // is this used?
    BoundIndex idx;   // The index in variable's bound list
    LVRef var;
    Delta delta;
    PtAsgn leq_pta;
public:
    LABound(BoundT type, PtAsgn leq_pta, LVRef var, const Delta& delta);
    inline void setIdx(BoundIndex i)  { idx = i; }
    inline BoundIndex getIdx() const { return idx; }
    inline const Delta& getValue() const { return delta; }
    inline BoundT getType() const { return { type }; }
    inline PTRef getPTRef() const { return leq_pta.tr;  }
    inline lbool getSign()  const { return leq_pta.sgn; }
    inline LVRef getLVRef() const { return var; }
};

class LABoundAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_bounds;
    static int laboundWord32Size() {
        return (sizeof(LABound)) / sizeof(uint32_t); }
public:
    LABoundAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_bounds(0) {}
    LABoundAllocator() : n_bounds(0) {}
    inline unsigned getNumBounds() const { return n_bounds; }

    LABoundRef alloc(BoundT type, PtAsgn leq_pta, LVRef var, const Delta& delta);
    inline LABound&       operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline const LABound& operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline LABound*       lea       (LABoundRef r)       { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
    inline const LABound* lea       (LABoundRef r) const { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
    inline LABoundRef     ael       (const LABound* t)   { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundRef rf; rf.x = r; return rf; }
    inline void printBound(const LABoundRef r) const { }
    inline void clear() {}
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
    inline bool           reloced   ()                 const { return reloc; }
    inline LABoundListRef relocation()                 const { return reloc_target; }
    inline void           relocate  (LABoundListRef r)       { reloc = 1; reloc_target = r; }
    inline unsigned       size      ()                 const { return sz; }
           LABoundRef     operator[](BoundIndex i)     const;
    inline LVRef          getVar    ()                 const { return v; }
    inline LABoundList              (LVRef v, const vec<LABoundRef>& bs);
};

class bound_lessthan {
    LABoundAllocator& ba;
public:
    bound_lessthan(LABoundAllocator& ba) : ba(ba) {}
    inline bool operator() (LABoundRef r1, LABoundRef r2) const { return ba[r1].getValue() < ba[r2].getValue(); }
};

class LABoundListAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_boundlists;
    static int boundlistWord32Size(int size) {
        return (sizeof(LABoundList) + (sizeof(LABoundRef)*size)) / sizeof(uint32_t); }
public:
    LABoundListAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_boundlists(0) {}
    LABoundListAllocator() : n_boundlists(0) {}

    void moveTo(LABoundListAllocator& to);

    LABoundListRef alloc(const LVRef v, const vec<LABoundRef>& bs);
    LABoundListRef alloc(LABoundList& from);
    inline LABoundList&       operator[](LABoundListRef r)       { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline const LABoundList& operator[](LABoundListRef r) const { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline LABoundList*       lea(LABoundListRef r)              { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
    inline const LABoundList* lea(LABoundListRef r) const        { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
    inline LABoundListRef     ael(const LABoundList* t)          { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundListRef rf; rf.x = r; return rf; }

    void free(LABoundListRef tid);
    void reloc(LABoundListRef& tr, LABoundListAllocator& to);
};

struct LABoundRefPair { LABoundRef pos; LABoundRef neg; };

class LABoundStore
{
    struct BoundInfo { LVRef v; LABoundRef b1; LABoundRef b2; PTId leq_id; };
    vec<BoundInfo> in_bounds;
    LABoundAllocator& ba;
    LABoundListAllocator& bla;
    LAVarAllocator& lva;
    LAVarStore& lavarStore;
    vec<LABoundRefPair> ptermToLABoundsRef;
    Logic& logic;
    LABoundRef LABoundRef_LB_MinusInf;
    LABoundRef LABoundRef_UB_PlusInf;
    LABoundListRef empty_bounds;
public:
    LABoundStore(LABoundAllocator& ba, LABoundListAllocator& bla, LAVarAllocator& lva, LAVarStore& lavstore, Logic& l) : ba(ba), bla(bla), lva(lva), lavarStore(lavstore), logic(l) {
        LABoundRef_LB_MinusInf = ba.alloc(bound_l, PtAsgn{ logic.getTerm_true(), l_True },  LVRef_Undef, Delta_MinusInf);
        LABoundRef_UB_PlusInf  = ba.alloc(bound_u, PtAsgn{ logic.getTerm_true(), l_True },  LVRef_Undef, Delta_PlusInf);
        vec<LABoundRef> tmp;
        tmp.push(LABoundRef_LB_MinusInf);
        tmp.push(LABoundRef_UB_PlusInf);
        empty_bounds = bla.alloc(LVRef_Undef, tmp);
    }
    LABoundRef plusInf() { return LABoundRef_UB_PlusInf; }
    LABoundRef minusInf() { return LABoundRef_LB_MinusInf; }
    void addBound(LVRef v, PTRef leq_tr, PTId leq_id, const Real& constr, BoundT bound_t);
    void buildBounds(vec<LABoundRefPair>& ptermToLABoundRef);
    inline LABoundRef getLowerBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].lbound()]; }
    inline LABoundRef getUpperBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].ubound()]; }
    inline LABoundRefPair getBoundRefPair(const PTRef leq) { return ptermToLABoundsRef[Idx(logic.getPterm(leq).getId())]; }
    inline LABound& operator[] (LABoundRef br) { return ba[br]; }
};


#endif
