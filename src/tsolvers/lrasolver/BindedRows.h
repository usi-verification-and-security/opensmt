#include "LARefs.h"

class BindedRow
{
public:
    LVRef var;
    int pos;
};

class BindedRows
{
    int sz;
    BindedRow rows[0];
public:
    BindedRow& operator[] (int i) { return rows[i]; }
    int size() const { return sz; }
    void add(LVRef v, int pos) {}
    void remove(LVRef v) {};
    void clear() {}
};

class OccAllocator
{
public:
    OccRef alloc(LVRef) { return OccRef_Undef; }
};


class BindedRowAllocator : public RegionAllocator<uint32_t>
{
public:
    BindedRows& operator[] (OccListRef r) { return (BindedRows&)RegionAllocator<uint32_t>::operator[](r.x); }
};

class BindedRowStore
{
public:
    void remove(LVRef v, int row) {};
};
