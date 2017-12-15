#ifndef BINDEDROWS_H
#define BINDEDROWS_H

#include "LARefs.h"
#include "LAVar.h"
#include "Vec.h"
#include "Map.h"
#include "Alloc.h"
#include "LRALogic.h"

struct BindedRow
{
    LVRef var;
    int pos;
};

class BindedRows
{
    friend class BindedRowsStore;
    vec<BindedRow> rows;
    Map<LVRef,int,LVRefHash> varToIdx;
    void remove(LVRef v);
public:
    BindedRow& operator[] (int i) { return rows[i]; }
    int size() const { return rows.size(); }
    void add(LVRef v, int pos) { assert(pos >= 0); assert(!varToIdx.has(v)); varToIdx.insert(v, rows.size()); rows.push({v, pos}); }
    void clear() { rows.clear(); varToIdx.clear(); }
};

class BindedRowsAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_rows;
    static int bindedrowsWord32Size() {
        return (sizeof(BindedRows)) / sizeof(uint32_t); }

public:
    BindedRowsAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_rows(0) {}
    BindedRowsAllocator()                   : n_rows(0) {}
    unsigned getNumRows() const { return n_rows; }

    OccListRef alloc()
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(bindedrowsWord32Size());
        OccListRef id = {v};
        new (lea(id)) BindedRows();
        n_rows++;
        return id;
    }
    BindedRows&       operator[](OccListRef r)       { return (BindedRows&)RegionAllocator<uint32_t>::operator[](r.x); }
    const BindedRows& operator[](OccListRef r) const { return (const BindedRows&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    BindedRows*       lea       (OccListRef r)         { return (BindedRows*)RegionAllocator<uint32_t>::lea(r.x); }
    const BindedRows* lea       (OccListRef r) const   { return (BindedRows*)RegionAllocator<uint32_t>::lea(r.x); }
    OccListRef        ael       (const BindedRows* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); OccListRef rf; rf.x = r; return rf; }
    void              free      (OccListRef r)         { RegionAllocator<uint32_t>::free(bindedrowsWord32Size()); }
    void       clear() {}
};

class BindedRowsStore {
private:
    LRALogic& logic;
    LAVarAllocator& lva;
    BindedRowsAllocator& bra;
    int debug_count;
public:
    BindedRowsStore(LRALogic& l, LAVarAllocator& lva, BindedRowsAllocator& bra) : logic(l), lva(lva), bra(bra), debug_count(0) {}
    void remove(LVRef v, LVRef target);
    void add(LVRef row, int pos, LVRef target);
    BindedRows& getBindedRows(LVRef v) { return bra[lva[v].getBindedRowsRef()]; }
};

#endif
