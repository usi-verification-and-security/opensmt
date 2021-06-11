/*******************************************************************************************[Map.h]
Copyright (c) 2006-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Map_h
#define Minisat_Map_h

#include "osmtinttypes.h"
#include "Vec.h"
#include <vector>

//=================================================================================================
// Default hash/equals functions
//

//template<class K> struct Hash  { uint32_t operator()(const K& k)               const { return hash(k);  } };
template<class K> struct Equal { bool     operator()(const K& k1, const K& k2) const { return k1 == k2; } };

//template<class K> struct DeepHash  { uint32_t operator()(const K* k)               const { return hash(*k);  } };
template<class K> struct DeepEqual { bool     operator()(const K* k1, const K* k2) const { return *k1 == *k2; } };

//static inline uint32_t hash(uint32_t x){ return x; }
//static inline uint32_t hash(uint64_t x){ return (uint32_t)x; }
//static inline uint32_t hash(int32_t x) { return (uint32_t)x; }
//static inline uint32_t hash(int64_t x) { return (uint32_t)x; }


//=================================================================================================
// Some primes
//

static const int nprimes          = 25;
static const int primes [nprimes] = { 31, 73, 151, 313, 643, 1291, 2593, 5233, 10501, 21013, 42073, 84181, 168451, 337219, 674701, 1349473, 2699299, 5398891, 10798093, 21596719, 43193641, 86387383, 172775299, 345550609, 691101253 };

//=================================================================================================
// Hash table implementation of Maps
//

//template<class K, class D, class H = Hash<K>, class E = Equal<K> >
template<class K, class D, class H, class E = Equal<K> >
class Map {
 public:
    struct Pair { K key; D data; };

 private:
    H          hash;
    E          equals;

    vec<Pair>* table;
    int        cap;
    int        size;

    // Don't allow copying (error prone):
    Map<K,D,H,E>&  operator = (Map<K,D,H,E>& other) = delete;
                   Map        (Map<K,D,H,E>& other) = delete;

    bool    checkCap(int new_size) const { return new_size > cap; }

    int32_t index  (const K& k) const { return hash(k) % cap; }
    void   _insert (const K& k, const D& d) {
        vec<Pair>& ps = table[index(k)];
        ps.push(); ps.last().key = k; ps.last().data = d; }

    void    rehash () {
        const vec<Pair>* old = table;

        int old_cap = cap;
        int newsize = primes[0];
        for (int i = 1; newsize <= cap && i < nprimes; i++)
           newsize = primes[i];

        table = new vec<Pair>[newsize];
        cap   = newsize;

        for (int i = 0; i < old_cap; i++){
            for (int j = 0; j < old[i].size(); j++){
                _insert(old[i][j].key, old[i][j].data); }}

        delete [] old;

        // printf(" --- rehashing, old-cap=%d, new-cap=%d\n", cap, newsize);
    }


 public:

    Map () : table(NULL), cap(0), size(0) {}
    Map (const H& h, const E& e) : hash(h), equals(e), table(NULL), cap(0), size(0) {}
    Map (Map&& o) noexcept : table(NULL), cap(0), size(0) { std::swap(hash, o.hash); std::swap(equals, o.equals); std::swap(table, o.table); std::swap(cap, o.cap); std::swap(size, o.size); }
    //    Map (Map<K,D,H,E>&& o) noexcept : cap(0), size(0) { std::swap(hash, o.hash); std::swap(equals, o.equals); std::swap(table, o.table); std::swap(cap, o.cap); std::swap(size, o.size); }
    ~Map () { delete [] table; }

    //Map<K,D,H,E>&  operator = (Map<K,D,H,E>&& o) { std::swap(hash, o.hash); std::swap(equals, o.equals); std::swap(table, o.table); std::swap(cap, o.cap); std::swap(size, o.size); return *this; }
    Map&  operator = (Map&& o) { std::swap(hash, o.hash); std::swap(equals, o.equals); std::swap(table, o.table); std::swap(cap, o.cap); std::swap(size, o.size); return *this; }

    // PRECONDITION: the key must already exist in the map.
    const D& operator [] (const K& k) const
    {
        assert(size != 0);
        const D*         res = NULL;
        const vec<Pair>& ps  = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k))
                res = &ps[i].data;
        assert(res != NULL);
        return *res;
    }

    // PRECONDITION: the key must already exist in the map.
    D& operator [] (const K& k)
    {
        assert(size != 0);
        D*         res = NULL;
        vec<Pair>& ps  = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k))
                res = &ps[i].data;
        assert(res != NULL);
        return *res;
    }

    // PRECONDITION: the key must *NOT* exist in the map.
    void insert (const K& k, const D& d) { if (checkCap(size+1)) rehash(); _insert(k, d); size++; }
    bool peek   (const K& k, D& d) const {
        if (size == 0) return false;
        const vec<Pair>& ps = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k)){
                d = ps[i].data;
                return true; } 
        return false;
    }

    bool has   (const K& k) const {
        if (size == 0) return false;
        const vec<Pair>& ps = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k))
                return true;
        return false;
    }

    void getKeys(vec<K>& out) const {
        if (size == 0) return;
        for (int i = 0; i < cap; i++) {
            if (table[i] == NULL) continue;
            for (int j = 0; j < table[i].size(); j++)
                out.push(table[i][j].key);
        }
    }
    void getKeysAndVals(vec<Pair>& out) const {
        if (size == 0) return;
        for (int i = 0; i < cap; i++) {
            if (table[i] == NULL) continue;
            for (int j = 0; j < table[i].size(); j++)
                out.push(table[i][j]);
        }
    }

    vec<Pair> getKeysAndVals() const {
        vec<Pair> out;
        if (size == 0) return {};
        for (int i = 0; i < cap; i++) {
            if (table[i] == NULL) continue;
            for (int j = 0; j < table[i].size(); j++)
                out.push(table[i][j]);
        }
        return out;
    }

    void getKeysAndValsPtrs(vec<Pair*>& out) {
        if (size == 0) return;
        for (int i = 0; i < cap; i++) {
            if (table[i] == NULL) continue;
            for (int j = 0; j < table[i].size(); j++)
                out.push(&table[i][j]);
        }
    }

    vec<Pair*> getKeysAndValsPtrs() {
        if (size == 0) return {};
        vec<Pair*> out;
        for (int i = 0; i < cap; i++) {
            if (table[i] == NULL) continue;
            for (int j = 0; j < table[i].size(); j++)
                out.push(&table[i][j]);
        }
        return out;
    }

    vec<const Pair*> getKeysAndValsPtrs() const {
        if (size == 0) return {};
        vec<const Pair*> out;
        for (int i = 0; i < cap; i++) {
            if (table[i] == NULL) continue;
            for (int j = 0; j < table[i].size(); j++)
                out.push(&table[i][j]);
        }
        return out;
    }

    // PRECONDITION: the key must exist in the map.
    void remove(const K& k) {
        assert(has(k));
        assert(table != NULL);
        vec<Pair>& ps = table[index(k)];
        int j = 0;
        for (; j < ps.size() && !equals(ps[j].key, k); j++);
        assert(j < ps.size());
        ps[j] = ps.last();
        ps.pop();
        size--;
    }

    void clear  () {
        cap = size = 0;
        delete [] table;
        table = NULL;
    }

    int  getSize() const { return size; }
    int  elems() const { return size; }
    int  bucket_count() const { return cap; }

    // NOTE: the hash and equality objects are not moved by this method:
    void moveTo(Map& other){
        delete [] other.table;

        other.table = table;
        other.cap   = cap;
        other.size  = size;

        table = NULL;
        size = cap = 0;
    }

    void copyTo(Map& other) const {
        if (other.table != NULL) delete [] other.table;
        other.table = new vec<Pair>[cap];
        for (int i = 0; i < cap; i++) {
            table[i].copyTo(other.table[i]);
        }
        other.cap = cap;
        other.size = size;
    }

    // NOTE: given a bit more time, I could make a more C++-style iterator out of this:
    const vec<Pair>& bucket(int i) const { return table[i]; }
};

template<class K, class D, class H, class E = Equal<K> >
class VecMap {
    static_assert(std::is_trivially_copyable<D>::value, "elements of mtl::VecMap vectors need to be trivially copyable");
public:
    struct Pair { K key; vec<D> data; };

 private:
    H          hash;
    E          equals;

    std::vector<Pair>* table;
    int        cap;
    int        size;

    // Don't allow copying (error prone):
    VecMap<K,D,H,E>&  operator = (VecMap<K,D,H,E>& ) = delete;
                   VecMap        (VecMap<K,D,H,E>& ) = delete;

    bool    checkCap(int new_size) const { return new_size > cap; }

    int32_t index  (const K& k) const { return hash(k) % cap; }
    void   _insert (const K& k, const vec<D>& d) {
        std::vector<Pair>& ps = table[index(k)];
        ps.emplace_back(); ps.back().key = k;
        d.copyTo(ps.back().data); }

    void    rehash () {
        const std::vector<Pair>* old = table;

        int old_cap = cap;
        int newsize = primes[0];
        for (int i = 1; newsize <= cap && i < nprimes; i++)
           newsize = primes[i];

        table = new std::vector<Pair>[newsize];
        cap   = newsize;

        for (int i = 0; i < old_cap; i++) {
            for (const auto & pair : old[i]) {
                _insert(pair.key, pair.data);
            }
        }

        delete [] old;

        // printf(" --- rehashing, old-cap=%d, new-cap=%d\n", cap, newsize);
    }

    
 public:

    VecMap () : table(NULL), cap(0), size(0) {}
    VecMap (const H& h, const E& e) : hash(h), equals(e), table(NULL), cap(0), size(0){}
    ~VecMap () { delete [] table; }

    // PRECONDITION: the key must already exist in the map.
    const vec<D>& operator [] (const K& k) const
    {
        assert(size != 0);
        const vec<D>*    res = NULL;
        const std::vector<Pair>& ps  = table[index(k)];
        for (const Pair& p : ps)
            if (equals(p.key, k))
                res = &p.data;
        assert(res != NULL);
        return *res;
    }

    // PRECONDITION: the key must already exist in the map.
    vec<D>& operator [] (const K& k)
    {
        assert(size != 0);
        vec<D>*    res = NULL;
        std::vector<Pair>& ps  = table[index(k)];
        for (Pair & p : ps)
            if (equals(p.key, k))
                res = &p.data;
        assert(res != NULL);
        return *res;
    }

    // PRECONDITION: the key must *NOT* exist in the map.
    void insert (const K& k, const vec<D>& d) { assert(not has(k)); if (checkCap(size+1)) rehash(); _insert(k, d); size++; }
    bool peek   (const K& k, vec<D>& d) const {
        if (size == 0) return false;
        const std::vector<Pair>& ps = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k)){
                ps[i].data.copyTo(d);
                return true; } 
        return false;
    }

    bool has(const K& k) const {
        if (size == 0) return false;
        const std::vector<Pair>& ps = table[index(k)];
        for (const Pair& p : ps)
            if (equals(p.key, k))
                return true;
        return false;
    }

    const vec<D>* getOrNull(const K& k) const {
        if (size == 0) return nullptr;
        const std::vector<Pair>& ps = table[index(k)];
        for (const Pair & p : ps)
            if (equals(p.key, k))
                return &p.data;
        return nullptr;
    }

    void getKeys(vec<K>& out) const {
        if (size == 0) return;
        for (auto i = 0; i < cap; i++) {
            for (const auto & pair : table[i]) {
                out.push(pair.key);
            }
        }
    }

    // PRECONDITION: the key must exist in the map.
    void remove(const K& k) {
        assert(table != NULL);
        std::vector<Pair>& ps = table[index(k)];
        int j = 0;
        for (; j < ps.size() && !equals(ps[j].key, k); j++);
        assert(j < ps.size());
        ps[j].key = ps.last().key;
        ps.last().data.copyTo(ps[j].data);
        ps.pop();
        size--;
    }

    void clear  () {
        cap = size = 0;
        delete [] table;
        table = NULL;
    }

    int  elems() const { return size; }
    int  bucket_count() const { return cap; }

    // NOTE: the hash and equality objects are not moved by this method:
    void moveTo(VecMap& other){
        delete [] other.table;

        other.table = table;
        other.cap   = cap;
        other.size  = size;

        table = NULL;
        size = cap = 0;
    }

    // NOTE: given a bit more time, I could make a more C++-style iterator out of this:
    const std::vector<Pair>& bucket(int i) const { return table[i]; }
};

template<class K, class D, class H, class E = Equal<K> >
class VecKeyMap {
 public:
    struct Pair { vec<K> key; D data; };

 private:
    H          hash;
    E          equals;

    vec<Pair>* table;
    int        cap;
    int        size;

    // Don't allow copying (error prone):
    VecKeyMap<K,D,H,E>&  operator = (VecKeyMap<K,D,H,E>& other) = delete;
                   VecKeyMap        (VecKeyMap<K,D,H,E>& other) = delete;

    bool    checkCap(int new_size) const { return new_size > cap; }

    int32_t index  (const vec<K>& k) const { return hash(k) % cap; }
    void   _insert (const vec<K>& k, const D& d) {
        vec<Pair>& ps = table[index(k)];
        ps.push(); k.copyTo(ps.last().key); ps.last().data = d; }

    void    rehash () {
        const vec<Pair>* old = table;

        int old_cap = cap;
        int newsize = primes[0];
        for (int i = 1; newsize <= cap && i < nprimes; i++)
           newsize = primes[i];

        table = new vec<Pair>[newsize];
        cap   = newsize;

        for (int i = 0; i < old_cap; i++){
            for (int j = 0; j < old[i].size(); j++){
                _insert(old[i][j].key, old[i][j].data); }}

        delete [] old;

        // printf(" --- rehashing, old-cap=%d, new-cap=%d\n", cap, newsize);
    }


 public:

    VecKeyMap  () : table(NULL), cap(0), size(0) {}
    VecKeyMap  (const H& h, const E& e) : hash(h), equals(e), table(NULL), cap(0), size(0){}
    ~VecKeyMap () { delete [] table; }

    // PRECONDITION: the key must already exist in the map.
    const D& operator [] (const vec<K>& k) const
    {
        assert(size != 0);
        const D*         res = NULL;
        const vec<Pair>& ps  = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k))
                res = &ps[i].data;
        assert(res != NULL);
        return *res;
    }

    // PRECONDITION: the key must already exist in the map.
    D& operator [] (const vec<K>& k)
    {
        assert(size != 0);
        D*         res = NULL;
        vec<Pair>& ps  = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k))
                res = &ps[i].data;
        assert(res != NULL);
        return *res;
    }

    // PRECONDITION: the key must *NOT* exist in the map.
    void insert (const vec<K>& k, const D& d) { if (checkCap(size+1)) rehash(); _insert(k, d); size++; }
    bool peek   (const vec<K>& k, D& d) const {
        if (size == 0) return false;
        const vec<Pair>& ps = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k)){
                d = ps[i].data;
                return true; } 
        return false;
    }

    bool contains(const vec<K>& k) const {
        if (size == 0) return false;
        const vec<Pair>& ps = table[index(k)];
        for (int i = 0; i < ps.size(); i++)
            if (equals(ps[i].key, k))
                return true;
        return false;
    }

    // PRECONDITION: the key must exist in the map.
    void remove(const vec<K>& k) {
        assert(table != NULL);
        vec<Pair>& ps = table[index(k)];
        int j = 0;
        for (; j < ps.size() && !equals(ps[j].key, k); j++);
        assert(j < ps.size());
        ps[j] = ps.last();
        ps.pop();
        size--;
    }

    void clear  () {
        cap = size = 0;
        delete [] table;
        table = NULL;
    }

    int  elems() const { return size; }
    int  bucket_count() const { return cap; }

    // NOTE: the hash and equality objects are not moved by this method:
    void moveTo(VecKeyMap& other){
        delete [] other.table;

        other.table = table;
        other.cap   = cap;
        other.size  = size;

        table = NULL;
        size = cap = 0;
    }

    // NOTE: given a bit more time, I could make a more C++-style iterator out of this:
    const vec<Pair>& bucket(int i) const { return table[i]; }
};

// A vector of maps.
template<class K, class D, class H, class E = Equal<K> >
class MapVec
{
    Map<K,D,H>* data;
    int sz;
    int cap;

    // Don't allow copying (error prone):
    MapVec<K,D,H>&  operator = (MapVec<K,D,H>& other) = delete;
    MapVec<K,D,H,E>            (MapVec<K,D,H,E>& other) = delete;

    // Helpers for calculating next capacity:
    static inline int  imax   (int x, int y) { int mask = (y-x) >> (sizeof(int)*8-1); return (x&mask) + (y&(~mask)); }
    //static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }
    static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }
public:
    // Constructors:
    MapVec()                                : data(NULL) , sz(0)   , cap(0)    { }
    explicit MapVec(int size)               : data(NULL) , sz(0)   , cap(0)    { growTo(size); }
    MapVec(int size, const Map<K,D,H>& pad) : data(NULL) , sz(0)   , cap(0)    { growTo(size, pad); }
   ~MapVec()                                                                   { clear(true); }

    // Pointer to first element:
    operator Map<K,D,H>*       (void)           { return data; }

    // Size operations:
    int      size     (void) const     { return sz; }
    uint32_t size_    (void) const     { assert(sz >= 0); return (uint32_t) sz; }
    void     shrink   (int nelems)     { assert(nelems <= sz); for (int i = 0; i < nelems; i++) sz--, data[sz].~Map<K,D,H>(); }
    void     shrink_  (int nelems)     { assert(nelems <= sz); sz -= nelems; }
    int      capacity (void) const     { return cap; }
    void     capacity (int min_cap) {
        if (cap >= min_cap) return;
        int add = imax((min_cap - cap + 1) & ~1, ((cap >> 1) + 2) & ~1);   // NOTE: grow by approximately 3/2
        if (add > INT_MAX - cap || (((data = (Map<K,D,H,E>*)::realloc(data, (cap += add) * sizeof(Map<K,D,H>))) == NULL) && errno == ENOMEM))
        throw OutOfMemoryException();
    }
    void     growTo   (int size);
    void     growTo   (int size, const Map<K,D,H>& pad);
    void     clear    (bool dealloc = false) {
        if (data != NULL) {
            for (int i = 0; i < sz; i++) data[i].~Map<K,D,H>();
            sz = 0;
            if (dealloc) free(data), data = NULL, cap = 0; }
    }
    void     reset    ();

    // Stack interface:
    void     push  (void)                   { if (sz == cap) capacity(sz+1); new (&data[sz]) Map<K,D,H>(); sz++; }
    void     push  (const MapVec& elem)     { if (sz == cap) capacity(sz+1); elem.moveTo(data[sz++]); }
    void     pop   (void)                   { assert(sz > 0); sz--, data[sz].~Map<K,D,H>(); }
    // NOTE: it seems possible that overflow can happen in the 'sz+1' expression of 'push()', but
    // in fact it can not since it requires that 'cap' is equal to INT_MAX. This in turn can not
    // happen given the way capacities are calculated (below). Essentially, all capacities are
    // even, but INT_MAX is odd.

    const Map<K,D,H>& last  (void) const        { return data[sz-1]; }
    Map<K,D,H>&       last  (void)              { return data[sz-1]; }

    // Vector interface:
    const Map<K,D,H>& operator [] (int index) const { return data[index]; }
    Map<K,D,H>&       operator [] (int index)       { return data[index]; }

    // Duplicatation (preferred instead):
    void copyTo(MapVec<K,D,H>& copy) const { copy.clear(); copy.growTo(sz); for (int i = 0; i < sz; i++) data[i].copyTo(copy[i]); }
    void moveTo(MapVec<K,D,H>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }
};

//=================================================================================================
#endif
