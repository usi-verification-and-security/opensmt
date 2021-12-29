#ifndef LABOUNDS_H
#define LABOUNDS_H

#include "Delta.h"
#include "LARefs.h"
#include "LAVar.h"
#include "Alloc.h"

//
// Bound index type.  The bounds are ordered in a list, and indexed using a number in the list.
// To determine if a given bound is higher than another, it suffices to check the current bound index
// and the new index.  However, we need special values for no lower bound and no upper bound.
//
// The values are a little special.  Two least significant bits encode whether this is the lowest
// bound, the highest bound, or a normal bound.  Lowest bound is 00, highest bound is 11, and
// normal bound is 01.
//

class LABound
{
    char type;    // Upper / lower
    unsigned bidx;     // The index in variable's bound list
    int id;       // The unique id of the bound
    LVRef var;
    Delta delta;
public:
    struct BLIdx { unsigned x; };
    LABound(BoundT type, LVRef var, Delta && delta, int id);
    inline void setIdx(BLIdx i)  { bidx = i.x; }
    inline BLIdx getIdx() const { return {bidx}; }
    inline const Delta& getValue() const { return delta; }
    inline BoundT getType() const { return { type }; }
    inline LVRef getLVRef() const { return var; }
    int getId() const { return id; }
};

class LABoundAllocator : public RegionAllocator<uint32_t>
{
    std::vector<LABoundRef> allocatedBounds;
    static int laboundWord32Size() { return (sizeof(LABound)) / sizeof(uint32_t); }
public:
    LABoundAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap) {}
    LABoundAllocator() {}
    ~LABoundAllocator() { clear(); }

    LABoundRef alloc(BoundT type, LVRef var, Delta && delta);
    inline LABound&       operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline const LABound& operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline LABound*       lea       (LABoundRef r)       { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
    inline const LABound* lea       (LABoundRef r) const { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
    inline LABoundRef     ael       (const LABound* t)   { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundRef rf; rf.x = r; return rf; }

    void clear() override {
        for (LABoundRef ref : allocatedBounds) {
            lea(ref)->LABound::~LABound();
        }
        allocatedBounds.clear();
        RegionAllocator<uint32_t>::clear();
    }
};

class bound_lessthan {
    LABoundAllocator& ba;
public:
    bound_lessthan(LABoundAllocator& ba) : ba(ba) {}
    inline bool operator() (LABoundRef r1, LABoundRef r2) const;
};


class LABoundRefPair {
public:
    LABoundRefPair(): pos{LABoundRef_Undef.x}, neg{LABoundRef_Undef.x} {}
    LABoundRefPair(LABoundRef pos, LABoundRef neg): pos{pos.x}, neg{neg.x} {}
    LABoundRef pos;
    LABoundRef neg;
    bool operator== (const LABoundRefPair& o) const { return (pos == o.pos) && (neg == o.neg); }
};

class LABoundStore
{
public:
    struct BoundInfo { LVRef v; LABoundRef ub; LABoundRef lb; };
    struct BoundValuePair {Delta upper; Delta lower; };
private:
    vec<BoundInfo> in_bounds;
    LABoundAllocator ba{1024};
    LAVarStore & lvstore;
    std::vector<vec<LABoundRef>> bounds;
public:
    LABoundStore(LAVarStore &lvstore) : lvstore(lvstore) {}
    void clear();
    inline LABound& operator[] (LABoundRef br) { return ba[br]; }
    inline const LABound& operator[] (LABoundRef br) const { return ba[br]; }

    void buildBounds();
    void updateBound(BoundInfo bi);
    vec<LABoundRef> const & getBounds(LVRef v) const { return bounds.at(getVarId(v)); }
    vec<LABoundRef> & getBounds(LVRef v) { return bounds.at(getVarId(v)); }
    LABoundRef getBoundByIdx(LVRef v, int it) const;
    bool isUnbounded(LVRef v) const;
    void ensureReadyFor(LVRef v);

    // Debug
    char* printBound(LABoundRef br) const; // Print the bound br
    char* printBounds(LVRef v) const; // Print all bounds of v


    // Allocates lower and upper bound for LA var with the given values
    BoundInfo allocBoundPair(LVRef v, BoundValuePair boundPair) {
        ensureReadyFor(v);
        LABoundRef ub = ba.alloc(bound_u, v, std::move(boundPair.upper));
        LABoundRef lb = ba.alloc(bound_l, v, std::move(boundPair.lower));
        in_bounds.push(BoundInfo{v, ub, lb});
        return in_bounds.last();
    }

    LAVarStore const& getVarStore() const { return lvstore; }
};


#endif
