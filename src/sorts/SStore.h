/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

#ifndef SSTORE_H
#define SSTORE_H

#include "SSort.h"
#include "Alloc.h"
#include "TypeUtils.h"


#include <unordered_map>
#include <iosfwd>


struct SortHash {
    uint32_t operator() (const SortKey& s) const {
        auto v = (uint32_t)s.sym.x;
        for (SRef arg : s.args) {
            v += (uint32_t)arg.x;
        }
        return v;
    }
};

class SStore
{
  private:
    SortAllocator sa {512};
    SortSymbolAllocator ssa {512};
    std::unordered_map<SortKey, SRef, SortHash> sortTable;
    std::unordered_map<std::string, SSymRef> sortSymbolTable;
    vec<SRef> sorts;
    vec<SSymRef> sortSymbols;
  public:

    SStore() = default;
    ~SStore() = default;

    //===========================================================================
    // Public APIs for sort construction/destruction

    bool peek(SortSymbol const & symbol, SSymRef & outRef) const;
    SSymRef newSortSymbol(SortSymbol symbol);

    Sort const & operator [](SRef sr)               const { return sa[sr]; }
    SortSymbol const & operator [](SSymRef sr)      const { return ssa[sr]; }

    opensmt::pair<SRef,bool> getOrCreateSort(SSymRef symbolRef, vec<SRef> && rest);
    SSymRef getSortSym(SRef sr) const { return sa[sr].getSymRef(); }
    std::string getSortSymName(SSymRef ssr) const { return ssa[ssr].name; }
    std::string getSortSymName(SRef sr) const { return getSortSymName(getSortSym(sr)); }
    unsigned int getSortSymSize(SSymRef ssr) const { return ssa[ssr].arity; }
    std::string printSort (SRef sr) const {
        std::string name = getSortSymName(sr);
        if (sa[sr].getSize() > 0) {
            name = "(" + name + " ";
            for (unsigned i = 0; i < sa[sr].getSize(); i++) {
                name += printSort(sa[sr][i]) + (i == sa[sr].getSize() - 1 ? "" : " ");
            }
            name += ")";
        }
        return name;
    }

    int  getSize(SRef sr) const { return sa[sr].getSize(); }
    const vec<SRef>& getSorts() const { return sorts; }
    const vec<SSymRef>& getSortSyms() const { return sortSymbols; }
    int     numSorts() const { return sorts.size(); }
};

#endif
