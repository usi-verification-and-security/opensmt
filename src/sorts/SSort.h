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


struct SSymRef {
    uint32_t x;
    SSymRef & operator= (uint32_t v) { x = v; return *this; }
    inline friend bool operator== (SSymRef a1, SSymRef a2) {return a1.x == a2.x; }
    inline friend bool operator!= (SSymRef a1, SSymRef a2) {return a1.x != a2.x; }
};

const static struct SSymRef SSymRef_Undef = {INT32_MAX};

struct SSymRefHash {
    uint32_t operator () (SSymRef s) const {
        return (uint32_t)s.x; }
};

struct SortSymbol {
    static constexpr unsigned int INTERNAL = 0x1;
    std::string name;
    unsigned int arity;
    unsigned int flags;
    SortSymbol(std::string name_, unsigned int arity) : name(std::move(name_)), arity(arity), flags(0) {};
    SortSymbol(std::string name_, unsigned int arity, unsigned int flags) : name(std::move(name_)), arity(arity), flags(flags) {};
    SortSymbol(SortSymbol &&) = default;
    SortSymbol(SortSymbol const &) = default;
    bool isInternal() const { return (flags & INTERNAL) != 0; };
};

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

using sortid_t = int;

class Sort {
  private:

    SSymRef  symRef;
    sortid_t    uniq_id;
    uint32_t size;
    SRef        args[0];
  public:
    Sort(SSymRef symRef_, sortid_t uniq_id_, vec<SRef> const & rest)
        : symRef(symRef_)
        , uniq_id(uniq_id_)
        , size(rest.size_())
    { for (int i = 0; i < rest.size(); i++) args[i] = rest[i]; }

    inline sortid_t getId() const { return uniq_id; };

    SSymRef getSymRef() const { return symRef; }

    uint32_t getSize() const { return size; }

    SRef operator[](uint32_t index) const { assert(index < size); return args[index]; }
};

struct SortKey {
    SSymRef sym;
    vec<SRef> args;
    SortKey(SSymRef _sym, vec<SRef> && _args) : sym(_sym), args(std::move(_args)) { }
    friend bool operator== (SortKey const & k1, SortKey const & k2) {
        if (k1.sym != k2.sym) return false;
        if (k1.args.size() != k2.args.size()) return false;
        for (int i = 0; i < k1.args.size(); i++)
            if (k1.args[i] != k2.args[i]) return false;
        return true;
    }
};

class SortSymbolAllocator : public RegionAllocator<uint32_t>
{
    static int SortSymbolWord32Size() {
        return sizeof(SortSymbol) / sizeof(uint32_t); }
public:
    SortSymbolAllocator() {}
    SortSymbolAllocator(uint32_t init_capacity): RegionAllocator<uint32_t>(init_capacity) {}
    SSymRef alloc(SortSymbol symbol)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(SortSymbolWord32Size());
        SSymRef sid {v};
        new (lea(sid)) SortSymbol(std::move(symbol));
        return sid;
    }
    SortSymbol&       operator[](SSymRef r)       { return (SortSymbol&)RegionAllocator<uint32_t>::operator[](r.x); }
    const SortSymbol& operator[](SSymRef r) const { return (SortSymbol&)RegionAllocator<uint32_t>::operator[](r.x); }
    SortSymbol*       lea       (SSymRef r)       { return (SortSymbol*)RegionAllocator<uint32_t>::lea(r.x); }

    void free(SSymRef)
    {
        RegionAllocator<uint32_t>::free(SortSymbolWord32Size());
    }
};

class SortAllocator : public RegionAllocator<uint32_t>
{
    sortid_t static_uniq_id = 0;
    static int SortWord32Size(int size) {
        return (sizeof(Sort) + size) / sizeof(uint32_t); }
  public:
    SortAllocator() {}
    SortAllocator(uint32_t init_capacity): RegionAllocator<uint32_t>(init_capacity) {}
    void moveTo(SortAllocator &to) {
        RegionAllocator<uint32_t>::moveTo(to); }
    SRef alloc(SortKey const & key)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(SortWord32Size(key.args.size()));
        SRef sid = {v};
        new (lea(sid)) Sort(key.sym, static_uniq_id++, key.args);
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
