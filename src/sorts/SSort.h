/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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


#ifndef SORT_H
#define SORT_H

#include "Vec.h"
#include "Alloc.h"

#include <string>

struct SRef {
    uint32_t x;
    SRef & operator= (uint32_t v) { x = v; return *this; }
    inline friend bool operator== (SRef a1, SRef a2) {return a1.x == a2.x; }
    inline friend bool operator!= (SRef a1, SRef a2) {return a1.x != a2.x; }
};

const static struct SRef SRef_Undef = {INT32_MAX};
const static struct SRef SRef_Nil   = {INT32_MAX-1};

struct SRefHash {
    uint32_t operator () (const SRef& s) const {
        return (uint32_t)s.x; }
};

struct SortSymbol {
    std::string name;
    SortSymbol(std::string name_) : name(std::move(name_)) {};
    SortSymbol(SortSymbol &&) = default;
};

using sortid_t = int;

class Sort {
  private:

    SortSymbol  idr;
    sortid_t    uniq_id;
    int         size;
    SRef        rest_sorts[0];
  public:
    Sort(SortSymbol idr_, sortid_t uniq_id_, vec<SRef> const & rest)
        : idr(std::move(idr_))
        , uniq_id(uniq_id_)
        , size(0)
    { for (int i = 0; i < rest.size(); i++) rest_sorts[i] = rest[i]; }

    int getSize() const { return size; }

    inline sortid_t getId() const { return uniq_id; };

    const char * getName() const { return idr.name.c_str(); }
};


class SortAllocator : public RegionAllocator<uint32_t>
{
    static sortid_t static_uniq_id;
    static int SortWord32Size(int size) {
        return (sizeof(Sort) + size) / sizeof(uint32_t); }
  public:
    SortAllocator() {}
    SortAllocator(uint32_t init_capacity): RegionAllocator<uint32_t>(init_capacity) {}
    void moveTo(SortAllocator &to) {
        RegionAllocator<uint32_t>::moveTo(to); }
    SRef alloc(SortSymbol id, vec<SRef> const & rest)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(SortWord32Size(rest.size()));
        SRef sid;
        sid.x = v;
        new (lea(sid)) Sort(std::move(id), static_uniq_id++, rest);
        return sid;
    }
    Sort&       operator[](SRef r)       { return (Sort&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Sort& operator[](SRef r) const { return (Sort&)RegionAllocator<uint32_t>::operator[](r.x); }
    Sort*       lea       (SRef r)       { return (Sort*)RegionAllocator<uint32_t>::lea(r.x); }
    Ref         ael       (const Sort* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(SRef sr)
    {
        Sort& s = operator[](sr);
        RegionAllocator<uint32_t>::free(SortWord32Size(s.getSize()));
    }
};



#endif // SORT_H
