#include "Delta.h"


struct LABoundRef
{
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LVRef& a1, const LVRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LVRef& a1, const LVRef& a2) { return a1.x != a2.x; }
}

static struct LABoundRef LABoundRef_Undef = { INT32_MAX };
static struct LABoundRef LABoundRef_Infty = { 0 };

struct BoundT {
    static const char* const names[3];
    char t;
    bool operator== (const BoundT& o) const { return o.t == t; }
    BoundT operator~ (const BoundT& o) const { return { 1-o.t }; }
    inline friend ostream& operator<< (ostream& o, const BoundT& b) { o << names[(int)b.t]; return o; }
};

const BoundT bound_l = { 0 };
const BoundT bound_u = { 1 };

class LABound
{
    struct {
        unsigned type    : 1;  // Upper / lower
        unsigned reverse : 1;  // is this used?
        unsigned active  : 1;  // is this used?
        unsigned idx     : 29; // The index in variable's bound list
    } header;
    Delta delta;
    PtAsgn leq_pta;
public:
    LABound(BoundT type, PtAsgn leq_pta, Delta& delta)
        : type(type.t), reverse(false), active(true), idx(536870911), leq_pta(leq_pta), delta(delta)
    {}
    void setIdx(int i)  { header.idx = i; }
    int  getIdx() const { return header.idx; }
    const Delta& getValue() const { return delta; }
    BoundT getType() const { return { header.type }; }
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

    LABoundRef alloc(BoundT type, PtAsgn leq_pta, Delta& delta)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
        LABoundRef id = {v};
        new (lea(id)) LABound(type, leq_pta, delta);
        return id;
    }
    LABound&       operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LABound& operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    void printBound(const LABoundRef r) const { }
};

class LABoundListRef
{
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LABoundListRef& a1, const LABoundListRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LABoundListRef& a1, const LABoundListRef& a2) { return a1.x != a2.x; }
}

static struct LABoundListRef LABoundListRef_Undef = { INT32_MAX };

class LABoundList
{
    unsigned size;
    LVRef v;
    LABoundRef bounds[0];
public:
    LABoundList(LVRef v, const vec<LABoundRef>& bs) : v(v), size(bs.size()) {
        for (int i = 0; i < v.size(); i++) bounds[i] = bs[i];
    }
};

class LABoundListAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_boundlists;
    static int boundlistWord32Size(int size) {
        return (sizeof(LABoundList) + (sizeof(LABoundRef)*size)) / sizeof(uint32_t); }
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
        new (lea(id)) LABoundListRef(v, bs);
        return id;
    }
    LABoundList&       operator[](LABoundListRef r)       { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LABoundList& operator[](LABoundListRef r) const { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
    LABoundList*       lea(LABoundListRef r)              { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
    const LABoundList* lea(LABoundListRef r) const        { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
    LABoundList        ael(const LABoundList* t)          { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundListRef rf; rf.x = r; return rf; }

    void free(LABoundListRef tid)
    {
        LABoundList& b = operator[](tid);
        RegionAllocator<uint32_t>::free(lawordlistWord32Size(b.size()));
    }
    void reloc(LABoundListRef& tr, LABoundListAllocator& to)
    {
        LABoundList& bl = operator[](tr);
        if (bl.reloced()) { tr = bl.relocation(); return; }
        tr = to.alloc(bl);
        bl.reloacate(tr);
        to[tr].size = bl.size;
        to[tr].v    = bl.v;
    }
};

class LABoundStore
{
    struct BoundInfo { LVRef v, LABoundRef b1, LABoundRef b2, PTId leq_id };
    vec<BoundInfo> in_bounds;
    LABoundAllocator ba;
    LABoundListAllocator bla;
public:
    void addBound(LVRef v, Real* constr, BoundT bound_t);
    void buildBounds(vec<LABoundRefPair>& ptermToLABoundRef);
    LABoundRef getLowerBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].lbound()]; }
    LABoundRef getUpperBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].ubound()]; }
};

struct LABoundRefPair { LABoundRef pos; LABoundRef neg; };

LABoundStore::addBound(LVRef v, PTRef leq_ref, PTId leq_id, Real* constr, BoundT bound_t)
{
    Delta *bound = NULL;
    Delta *boundRev = NULL;
    Delta::deltaType bound_type;
    bound = new Delta(constr);

    if (bound_t == bound_u)
        boundRev = new Delta(v, 1);
    else
        boundRev = new Delta(v, -1);

    LABoundRef br_pos = ba.alloc(bound_t, PtAsgn(leq_ref, true), bound);
    LABoundRef br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, false), boundRev);

    in_bounds.add(BoundInfo(v, br_pos, br_neg, leq_id));
}


void LABoundStore::buildBounds(vec<LABoundRefPair>& ptermToLABoundRefs)
{
    Map<LVRef, LABoundRef> bounds_map;

    for (int i = 0; i < in_bounds.size(); i++) {
        if (!bounds_map.has(in_bounds[i].v))
            bounds_map.insert(v, vec<int>());
        bounds_map[v].push(in_bounds[i]);
        while (ptermToLABoundsRef.size() <= in_bounds[i].leq_id)
            ptermToLABoundsRef.push({ LABoundRef_Undef, LABoundRef_Undef });
        ptermToLABoundsRefs[leq_id] = { br_pos, br_neg };
    }
    vec<LVRef> &keys = bounds_map.keys();
    for (int i = 0; i < keys.size(); i++) {
        LABoundListRef br = bla.alloc(keys[i], bounds_map[keys[i]]);
        sort(bla[br]);
        for (int j = 0; j < bla[br].size(); j++)
            bla[br][j].setIdx(j);
    }
}
