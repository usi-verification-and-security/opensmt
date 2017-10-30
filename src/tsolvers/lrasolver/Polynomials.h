struct PolyRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const PolyRef& a1, const PolyRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const PolyRef& a1, const PolyRef& a2) { return a1.x != a2.x; }
};

static struct PolyRef PolyRef_Undef = { INT32_MAX };

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
    int size() { return sz; }
};

class PolyAllocator : RegionAllocator<uint32_t>
{
public:
    Poly& operator[] (PolyRef pr) { return (PolyRef&)RegionAllocator<uint32_t>::operator[](p.x); }

};



class PolyStore
{
public:
    PolyRef getPolynomial(LVRef s) { return PolyRef_Undef; }
};
