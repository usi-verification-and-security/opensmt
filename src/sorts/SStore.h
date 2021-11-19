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

struct SortKey {
    SSymRef sym;
    vec<SRef> args;
    friend bool operator== (const SortKey& k1, const SortKey& k2) {
        if (k1.sym != k2.sym) return false;
        if (k1.args.size() != k2.args.size()) return false;
        for (int i = 0; i < k1.args.size(); i++)
            if (k1.args[i] != k2.args[i]) return false;
        return true;
    }
};

struct SortHash {
    uint32_t operator () (const SortKey& s) const {
        uint32_t v = (uint32_t)s.sym.x;
        for (int i = 0; i < s.args.size(); i++) {
            v += (uint32_t)s.args[i].x;
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
  public:

    SStore() = default;
    ~SStore() = default;

    //===========================================================================
    // Public APIs for sort construction/destruction

    bool peek(SortSymbol const & symbol, SSymRef & outRef);
    SSymRef newSortSymbol(SortSymbol symbol);

    Sort const & operator [](SRef sr)               const { return sa[sr]; }
    SortSymbol const & operator [](SSymRef sr)      const { return ssa[sr]; }

    opensmt::pair<SRef,bool> getOrCreateSort(SSymRef symbolRef, vec<SRef> const & rest);
    std::string const & getName (SRef sr) const { return ssa[sa[sr].getSymRef()].name; }
    const vec<SRef>& getSorts() const { return sorts; }
    int     numSorts() const { return sorts.size(); }
    void dumpSortsToFile(std::ostream&);
};

#endif
