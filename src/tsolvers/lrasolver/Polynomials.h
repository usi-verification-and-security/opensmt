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
    const PolyTerm& operator[](PolyTermRef r) const { return (PolyTerm&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    PolyTerm*       lea       (PolyTermRef r)         { return (PolyTerm*)RegionAllocator<uint32_t>::lea(r.x); }
    const PolyTerm* lea       (PolyTermRef r) const   { return (PolyTerm*)RegionAllocator<uint32_t>::lea(r.x); }
    PolyTermRef     ael       (const PolyTerm* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); PolyTermRef rf; rf.x = r; return rf; }
    void            clear     () {};
    void            free      (PolyTermRef t) {
        RegionAllocator<uint32_t>::free(polytermWord32Size());
    }
    void updateCoef (PolyTermRef r, const opensmt::Real& coef) { getPolyTerm(r).coef = coef; }
    void updateVar  (PolyTermRef r, LVRef v) { getPolyTerm(r).var = v; } // Use with care, also the index info in the poly needs to be updated
private:
    PolyTerm& getPolyTerm (PolyTermRef r) { return (PolyTerm&)RegionAllocator<uint32_t>::operator[](r.x); }
};

class PolyStore;

class Poly
{
private:
    int sz;
    int cap;
    int id;
    LVRef var;
    PolyTermRef terms[0];
public:
    Poly(vec<PolyTermRef>& ps, LVRef var, int id);
    Poly(Poly& old, int new_cap);
    int          getId() const { return id; }
    LVRef        getVar() const { return var; }
    PolyTermRef& operator[] (int i) { return terms[i]; }
    int          size() const { return sz; }
    int          getUnusedCap() { return cap - sz; }
    void         append(PolyTermRef tr, LVRef var) { if (sz < cap) { terms[sz++] = tr; } else assert(false); }
    friend class PolyAllocator;
    friend class PolyStore;
};

class PolyAllocator : RegionAllocator<uint32_t>
{
    PolyTermAllocator& pta;
    int id_count;
    static int polyWord32Size(int size) {
        return (sizeof(Poly) + (sizeof(PolyTermRef) * size )) / sizeof(uint32_t); }
public:
    explicit PolyAllocator(PolyTermAllocator& pta) : pta(pta), id_count(0) {}
    PolyRef alloc(vec<PolyTermRef>& pts, LVRef var) {
        uint32_t v = RegionAllocator<uint32_t>::alloc(polyWord32Size(pts.size()));
        PolyRef id = {v};
        new (lea(id)) Poly(pts, var, id_count++);
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
    MapVec<LVRef,int,LVRefHash> varToIdx;
    bool checkConsistency(PolyRef pr);
//    vec<LVRef> cols;
//    vec<LVRef> rows;
public:
    PolyStore(LAVarAllocator& lva, PolyAllocator& pa, BindedRowsStore& brs, LRALogic& logic) : lva(lva), pa(pa), pta(pa.pta), brs(brs), logic(logic) {}
    PolyRef getPolyRef (LVRef s)                          { return lva[s].getPolyRef(); }
    Poly&   getPoly    (LVRef s)                          { return pa[getPolyRef(s)]; }
    PolyRef makePoly   (LVRef s, vec<PolyTermRef>& terms);
    void  remove       (LVRef var, PolyRef pol); // Removes var from pol
    void  remove       (LVRef poly_var);         // Removes the polynomial corresponding to poly_var
    void  remove       (PolyRef pr);             // Removes the polynomial pr
    int   add          (PolyRef pr, LVRef v, Real &c);
    void  updateTerm   (PolyRef pr, PolyTermRef term, LVRef var, const opensmt::Real& coef);  // Update the polytermref old to contain var * coef in pr.
    void  updateVar    (PolyRef pr, LVRef v) { pa[pr].var = v; } // Update the var of the polynomial (i.e. v_old = p(x), update v := var)
    void  updateCoef   (PolyTermRef ptr, const opensmt::Real& coef) { pta.updateCoef(ptr, coef); }
    char* printPolyTerm(const opensmt::Real &coef, LVRef var);
    char* printPoly    (PolyRef pr);
    char* printOccurrences(LVRef var);
    bool  has          (PolyRef pr, LVRef v) { return varToIdx[pa[pr].getId()].has(v); }
    PolyTermRef find   (PolyRef pr, LVRef v) { return pa[pr][varToIdx[pa[pr].getId()][v]]; }
    int   getPos       (PolyRef pr, LVRef v) { return varToIdx[pa[pr].getId()][v]; }
};


