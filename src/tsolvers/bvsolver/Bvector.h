/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2017 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef BVECTOR_H
#define BVECTOR_H
#include "Vec.h"
#include "Alloc.h"
#include "PTRef.h"

#include "Map.h"

struct BVRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const BVRef& a1, const BVRef& a2)   { return a1.x == a2.x; }
    inline friend bool operator!= (const BVRef& a1, const BVRef& a2)   { return a1.x != a2.x; }
    inline friend bool operator< (const BVRef& a1, const BVRef& a2)    { return a1.x > a2.x;  }
};

static struct BVRef BVRef_Undef = {INT32_MAX};

struct BVRefHash {
    uint32_t operator () (const BVRef& s) const {
        return (uint32_t)s.x; }
};

template <>
struct Equal<const BVRef> {
    bool operator() (const BVRef& s1, const BVRef& s2) const { return s1 == s2; }
};
typedef uint32_t BVId; // Used as an array index

struct NameAsgn {
    PTRef name;
    PTRef asgn;
};

class Bvector {
    struct {
        unsigned is_signed  : 1;
        unsigned has_extra  : 1;
        unsigned reloced    : 1;
        unsigned size       : 29; }     header;
    BVId                                id;
    PTRef                               actVar;
    // This has to be the last
    PTRef                               args[0]; // Either the terms or the relocation reference

    friend class BvectorAllocator;
    friend class BVStore;
    friend void  bvSort(Bvector&);

  public:

    Bvector(const vec<PTRef>& ps, PTRef actVar) : actVar(actVar) {
        header.is_signed = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) args[i] = ps[i];
    }

    Bvector(vec<PTRef> const & ps) : Bvector(ps, PTRef_Undef) {}

    Bvector() : actVar(PTRef_Undef) {
        header.is_signed = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.size      = 0;
    }

    Bvector&    operator=   (Bvector const &) = delete;

    int      size        ()          const   { return header.size; }
    PTRef    getActVar   ()          const   { return actVar; }

    const PTRef&    operator [] (int i) const   { assert(i < size()); return args[i]; }
    PTRef&          operator [] (int i)         { assert(i < size()); return args[i]; }
    const PTRef&    lsb         ()      const   { return operator[](0); }
    const PTRef&    msb         ()      const   { return operator[](size()-1); }

    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new terms in the same Pterm allocator
     * @return A pointer to the first child of the term
     */
    const PTRef* begin() const { return args; }
    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new terms in the same Pterm allocator
     * @return A pointer to right past the last child of the term
     */
    const PTRef* end() const { return args + size(); }

    bool     reloced     ()      const   { return header.reloced; }
    BVRef    relocation  ()      const   { return { args[0].x }; }
    void     relocate    (BVRef t)       { header.reloced = 1; args[0] = {t.x}; }
    bool     is_signed   ()      const   { return header.is_signed; }
    void     set_signed  (bool m)    { header.is_signed = m; }

    int      getId() const { return id; }
    void     setId(int i) { id = i; }

    void     shrink(int s)               { header.size -= s; }
    void     copyTo(Bvector& to);
};

class BvectorAllocator : public RegionAllocator<uint32_t>
{
    BVId n_terms;
    void setNumBitVectors(int i) { n_terms = i; }
    static int ptermWord32Size(int size){
        return (sizeof(Bvector) + (sizeof(PTRef) * size )) / sizeof(uint32_t); }
 public:

    BvectorAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_terms(0) {}
    BvectorAllocator() : n_terms(0) {}

    int getNumTerms() const { return n_terms; }

    void moveTo(BvectorAllocator& to){
        to.n_terms = n_terms;
        RegionAllocator<uint32_t>::moveTo(to); }

    BVRef alloc(vec<PTRef> const & asgn, PTRef act_var) {
        assert(sizeof(PTRef) == sizeof(uint32_t));
        uint32_t v = RegionAllocator<uint32_t>::alloc(ptermWord32Size(asgn.size()));
        BVRef tid = {v};
        new (lea(tid)) Bvector(asgn, act_var);
        operator[](tid).setId(n_terms++);
        return tid;
    }

    BVRef alloc(Bvector&, bool) = delete;

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Bvector&       operator[](BVRef r)         { return (Bvector&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Bvector& operator[](BVRef r) const   { return (Bvector&)RegionAllocator<uint32_t>::operator[](r.x); }
    Bvector*       lea       (BVRef r)         { return (Bvector*)RegionAllocator<uint32_t>::lea(r.x); }
    const Bvector* lea       (BVRef r) const   { return (Bvector*)RegionAllocator<uint32_t>::lea(r.x); }
    BVRef          ael       (const Bvector* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); BVRef rf{r}; return rf; }

    void free(BVRef tid) {
        Bvector& t = operator[](tid);
        RegionAllocator<uint32_t>::free(ptermWord32Size(t.size()));
    }
    friend class BVStore;
};
#endif
