struct OccListRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const OccListRef& a1, const OccListRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const OccListRef& a1, const OccListRef& a2) { return a1.x != a2.x; }
};

struct OccRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const OccRef& a1, const OccRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const OccRef& a1, const OccRef& a2) { return a1.x != a2.x; }
};

static struct OccRef OccRef_Undef = { INT32_MAX };


class BindedRow
{
public:
    LVRef var;
    int pos;
};

class BindedRows
{
    int sz;
    rows BindedRow[0];
public:
    BindedRow& operator[] (int i) { return rows[i]; }
    int size() const { return sz; }
    void add(LVRef v, int pos) {}
    void remove(LVRef v) {};
};

class OccAllocator
{
public:
    OccRef alloc(LVRef) { return OccRef_Undef; }
};


class BindedRowAllocator : public RegionAllocator<uint32_t>
{
    BindedRows& operator[] (OccListRef r) { return (BindedRows&)RegionAllocator<uint32_t>::operator[](r.x); }
};

class BindedRowStore
{
public:
    void remove(LVRef v, int row) {};
};
