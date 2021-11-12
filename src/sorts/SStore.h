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


#include <unordered_map>
#include <iosfwd>

class SStore
{
  private:
    SortAllocator sa {512};
    std::unordered_map<std::string, SRef> sortTable;
    vec<SRef> sorts;
  public:

    SStore() = default;
    ~SStore() = default;

    //===========================================================================
    // Public APIs for sort construction/destruction

    bool    contains        (std::string const & s) const { return sortTable.find(s) != sortTable.end(); }
    bool    contains        (Sort const & s)        const { return contains(s.getName()); }
    SRef    operator []     (std::string const & s) const { return sortTable.at(s); }
    SRef    operator []     (Sort const & s)        const { return (*this)[s.getName()]; }
    Sort const * operator [](SRef sr)               const { return &sa[sr]; }

    SRef    newSort         (Identifier id, vec<SRef> const & rest);
    const char* getName     (SRef sr) const { return sa[sr].getName(); }
    Sort&   getSort         (SRef sr) { return sa[sr]; }
    const vec<SRef>& getSorts() const { return sorts; }
    int     numSorts() const { return sorts.size(); }
    void dumpSortsToFile(std::ostream&);
};

#endif
