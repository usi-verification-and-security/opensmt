#include <Alloc.h>
#include "LARefs.h"
#include "Global.h"
#include "Vec.h"
#include "Map.h"
#include "Alloc.h"
#include "Pterm.h"
#include "LAVar.h"
#include "BindedRows.h"
#include <ostream>

struct PolyTerm
{
    opensmt::Real coef;
    LVRef var;
};

class PolyTermAllocator : RegionAllocator<uint32_t> {
    uint32_t polytermWord32Size() { return sizeof(PolyTerm)/4; }
public:
    PolyTermRef alloc(opensmt::Real& coef, LVRef var)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(polytermWord32Size());
        PolyTermRef id = {v};
        new (lea(id)) PolyTerm{coef, var};
        return id;
    }
    PolyTerm& operator[] (PolyTermRef r) { return (PolyTerm&)RegionAllocator<uint32_t>::operator[](r.x); }
    const PolyTerm& operator[](PolyTermRef r) const { return (PolyTerm&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    PolyTerm*       lea       (PolyTermRef r)         { return (PolyTerm*)RegionAllocator<uint32_t>::lea(r.x); }
    const PolyTerm* lea       (PolyTermRef r) const   { return (PolyTerm*)RegionAllocator<uint32_t>::lea(r.x); }
    PolyTermRef     ael       (const PolyTerm* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); PolyTermRef rf; rf.x = r; return rf; }
    void            clear     () {};
    void            free      (PolyTermRef t) {
        RegionAllocator<uint32_t>::free(polytermWord32Size());
    }
};

class PolyStore;

class Poly
{
private:
    Map<LVRef,int,LVRefHash> varToIdx;
    int sz;
    int cap;
    PolyTermRef terms[0];
public:
    Poly(vec<PolyTermRef>& ps, PolyTermAllocator& pta) {
        for (int i = 0; i < ps.size(); i++) {
            terms[i] = ps[i];
            varToIdx.insert(pta[terms[i]].var, i);
        }
        cap = sz = ps.size();
    }
    Poly(Poly& old, int new_cap);
    PolyTermRef operator[] (int i) const { return terms[i]; }
    bool has(LVRef v) const { return varToIdx.has(v); }
    PolyTermRef find(LVRef v) const { return terms[varToIdx[v]]; }
    int getPos(LVRef v) const { return varToIdx[v]; }
    int size() const { return sz; }
    void remove(LVRef v);
    int getUnusedCap() { return cap - sz; }
    void append(PolyTermRef tr) { if (sz < cap) { terms[sz] = tr;  sz ++; } else assert(false); }
    friend class PolyStore;
};

class PolyAllocator : RegionAllocator<uint32_t>
{
    PolyTermAllocator& pta;
    static int polyWord32Size(int size) {
        return (sizeof(Poly) + (sizeof(PolyTermRef) * size )) / sizeof(uint32_t); }
public:
    explicit PolyAllocator(PolyTermAllocator& pta) : pta(pta) {}
    PolyRef alloc(vec<PolyTermRef>& pts) {
        uint32_t v = RegionAllocator<uint32_t>::alloc(polyWord32Size(pts.size()));
        PolyRef id = {v};
        new (lea(id)) Poly(pts, pta);
        return id;
    }
    // Allocate a new Poly with the same contents as r but with capacity new_cap >= [r].size()
    PolyRef alloc(PolyRef r, int new_cap) {
        uint32_t v = RegionAllocator<uint32_t>::alloc(polyWord32Size(new_cap));
        PolyRef id = {v};
        new (lea(id)) Poly(operator[](r), new_cap);
        return id;
    }
    Poly& operator[] (PolyRef r) { return (Poly&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Poly& operator[](PolyRef r) const { return (Poly&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Poly*       lea       (PolyRef r)         { return (Poly*)RegionAllocator<uint32_t>::lea(r.x); }
    const Poly* lea       (PolyRef r) const   { return (Poly*)RegionAllocator<uint32_t>::lea(r.x); }
    PolyRef     ael       (const Poly* t)     { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); PolyRef rf; rf.x = r; return rf; }
    void        free      (PolyRef r)         { RegionAllocator<uint32_t>::free(polyWord32Size(operator[] (r).size())); }
    void        clear()                       {}
    friend class PolyStore;
};



class PolyStore
{
    LAVarAllocator& lva;
    PolyAllocator& pa;
    PolyTermAllocator& pta;
    LRALogic& logic;
    BindedRowsStore& brs;
//    vec<LVRef> cols;
//    vec<LVRef> rows;
public:
    PolyStore(LAVarAllocator& lva, PolyAllocator& pa, BindedRowsStore& brs, LRALogic& logic) : lva(lva), pa(pa), pta(pa.pta), brs(brs), logic(logic) {}
    PolyRef getPolyRef(LVRef s)                          { return lva[s].getPolyRef(); }
    Poly&   getPoly   (LVRef s)                          { return pa[getPolyRef(s)]; }
    PolyRef makePoly  (LVRef s, vec<PolyTermRef>& terms) { PolyRef pr = pa.alloc(terms); lva[s].setPolyRef(pr); return pr; }
    void remove       (LVRef var, PolyRef pol); // Removes var from pol
    void remove       (LVRef poly_var);         // Removes the polynomial corresponding to poly_var
    int add           (LVRef poly_var, LVRef v, Real &c);
    void update       (PolyRef pr, PolyTermRef old, LVRef var, const opensmt::Real& coef);  // Update the polytermref old to contain var * coef in pr.
    char* printPolyTerm(const opensmt::Real &coef, LVRef var);
    char* printPoly   (PolyRef pr);
};


