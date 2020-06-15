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
    int bidx;     // The index in variable's bound list
    int id;       // The unique id of the bound
    LVRef var;
    Delta delta;
public:
    struct BLIdx { int x; };
    LABound(BoundT type, LVRef var, const Delta& delta, int id);
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

    LABoundRef alloc(BoundT type, LVRef var, const Delta& delta);
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

class LABoundList
{
    friend class LABoundListAllocator;
    friend class LABoundStore; // Needed so that I can sort the bounds in the list
    LVRef          v; // Do we need this?
    struct {
        unsigned reloc   : 1;
        unsigned sz      : 31;
    };
    LABoundListRef reloc_target;
    LABoundRef     bounds[0];
public:
    inline bool           reloced   ()                 const ;
    inline LABoundListRef relocation()                 const ;
    inline void           relocate  (LABoundListRef r)   ;
    inline unsigned       size      ()                 const ;
           LABoundRef     operator[](int i)            const;
    inline LVRef          getVar    ()                 const ;
    inline LABoundList              (LVRef v, const vec<LABoundRef>& bs);
};

class bound_lessthan {
    LABoundAllocator& ba;
public:
    bound_lessthan(LABoundAllocator& ba) : ba(ba) {}
    inline bool operator() (LABoundRef r1, LABoundRef r2) const;
};

class LABoundListAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_boundlists;
    static int boundlistWord32Size(int size);
public:
    LABoundListAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_boundlists(0) {}
    LABoundListAllocator() : n_boundlists(0) {}

    void moveTo(LABoundListAllocator& to);

    LABoundListRef alloc(const LVRef v, const vec<LABoundRef>& bs);
    LABoundListRef alloc(LABoundList& from);
    inline LABoundList&       operator[](LABoundListRef r)   ;
    inline const LABoundList& operator[](LABoundListRef r) const;
    inline LABoundList*       lea(LABoundListRef r)        ;
    inline const LABoundList* lea(LABoundListRef r) const  ;
    inline LABoundListRef     ael(const LABoundList* t)    ;

    void free(LABoundListRef tid);
    void reloc(LABoundListRef& tr, LABoundListAllocator& to);
    void clear() override { RegionAllocator<uint32_t>::clear(); n_boundlists = 0; }
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
    LABoundListAllocator bla{1024};
    vec<LABoundListRef> var_bound_lists;
    LAVarStore &lvstore;
public:
    LABoundStore(LAVarStore &lvstore) : lvstore(lvstore) {}
    void buildBounds();
    void clear();
    void updateBound(BoundInfo bi); // Update a single bound.
//    inline LABoundRef getLowerBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].lbound()]; }
//    inline LABoundRef getUpperBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].ubound()]; }
    inline LABound& operator[] (LABoundRef br) { return ba[br]; }
    inline const LABound& operator[] (LABoundRef br) const { return ba[br]; }
    // Debug
    char* printBound(LABoundRef br) const; // Print the bound br
    char* printBounds(LVRef v) const; // Print all bounds of v
    LABoundListRef getBounds(LVRef v) const;
    LABoundRef getBoundByIdx(LVRef v, int it) const;
    int getBoundListSize(LVRef v) ;
    bool isUnbounded(LVRef v) const;

    // Allocates lower and upper bound for LA var with the given values
    BoundInfo allocBoundPair(LVRef v, BoundValuePair boundPair) {
        LABoundRef ub = ba.alloc(bound_u, v, std::move(boundPair.upper));
        LABoundRef lb = ba.alloc(bound_l, v, std::move(boundPair.lower));
        in_bounds.push(BoundInfo{v, ub, lb});
        return in_bounds.last();
    }

    LAVarStore const& getVarStore() const { return lvstore; }
};


#endif
