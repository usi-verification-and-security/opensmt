#include "LARefs.h"

struct PolyTerm
{
    Real coef;
    LVRef var;
};

class Poly
{
    PolyTerm terms[0];
    int sz;
public:
    PolyTerm& operator[] (int i) { return terms[i]; }
    bool has(LVRef v) { return false; }
    PolyTerm& find(LVRef v) { return terms[0]; }
    int add(LVRef, Real* c) { return 0; }
    void remove(LVRef v) {}
    int getPos(LVRef v) { return 0; }
    void setPos(LVRef v, int i) {}
    int size() { return sz; }
};

class PolyAllocator : RegionAllocator<uint32_t>
{
public:
    Poly& operator[] (PolyRef r) { return (Poly&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Poly& operator[](PolyRef r) const { return (Poly&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Poly*       lea       (PolyRef r)         { return (Poly*)RegionAllocator<uint32_t>::lea(r.x); }
    const Poly* lea       (PolyRef r) const   { return (Poly*)RegionAllocator<uint32_t>::lea(r.x); }
    PolyRef     ael       (const Poly* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); PolyRef rf; rf.x = r; return rf; }
    void        clear() {}
};



class PolyStore
{
public:
    PolyRef getPoly(LVRef s) { return PolyRef_Undef; }
    PolyRef makePoly(LVRef s, PTRef sum_tr) { return PolyRef_Undef; }
};
