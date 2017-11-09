#ifndef BINDEDROWS_H
#define BINDEDROWS_H

#include "LARefs.h"

struct BindedRow
{
    LVRef var;
    int pos;
};

class BindedRows
{
    vec<BindedRow> rows;
    Map<LVRef,int,LVRefHash> varToIdx;
public:
    BindedRow& operator[] (int i) { return rows[i]; }
    int size() const { return rows.size(); }
    void add(LVRef v, int pos) { assert(!varToIdx.has(v)); varToIdx.insert(v, rows.size()); rows.push({v, pos}); }
    void remove(LVRef v) { for (int i = varToIdx[v]+1; i < rows.size(); i++) { rows[i-1] = rows[i]; varToIdx[rows[i-1].var] = i-1; } rows.shrink(1); varToIdx.remove(v); };
    void clear() { rows.clear(); varToIdx.clear(); }
};

class OccAllocator
{
public:
    OccRef alloc(LVRef) { return OccRef_Undef; }
};


class BindedRowsAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_rows;
    static int bindedrowsWord32Size() {
        return (sizeof(BindedRows)) / sizeof(uint32_t); }public:

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
    void       clear() {}
};
#endif
