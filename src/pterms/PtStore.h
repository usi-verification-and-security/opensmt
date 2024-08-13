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

#ifndef PTSTORE_H
#define PTSTORE_H

#include "Pterm.h"

#include <symbols/SymStore.h>

#include <unordered_map>

namespace opensmt {
class SStore; // forward declaration

class PtermIter {
public:
    PtermIter(vec<PTRef> & in) : i(0), idToPTRef(in) {}
    PTRef operator*();              /* {
                     if (i < idToPTRef.size())
                         return idToPTRef[i];
                     else
                         return PTRef_Undef;
                 }*/
    PtermIter const & operator++(); // { i++; return *this; }
private:
    int i;
    vec<PTRef> & idToPTRef;
};

class PtStore {
public:
    PtStore(SymStore & symstore) : symstore(symstore) {}

    PTRef newTerm(SymRef const sym, vec<PTRef> const & ps); /* {
          PTRef tr = pta.alloc(sym, ps); idToPTRef.push(tr);
          assert(idToPTRef.size() == pta.getNumTerms());
          return tr;
      }*/

    void free(PTRef r); // { pta.free(r); }  // this is guaranteed to be lazy

    bool isAmbiguousNullarySymbolName(std::string_view name) const;
    vec<SymRef> getHomonymousNullarySymbols(std::string_view name) const;
    SymRef lookupSymbol(char const * s, vec<PTRef> const & args, SymbolMatcher symbolMatcher = SymbolMatcher::Any,
                        SRef sort = SRef_Undef);

    Pterm & operator[](PTRef tr);             // { return pta[tr]; }
    Pterm const & operator[](PTRef tr) const; // { return pta[tr]; }

    bool hasCtermKey(SymRef & k);             // { return cterm_map.has(k); }
    void addToCtermMap(SymRef & k, PTRef tr); /* {
          cterm_map.insert(k, tr);
  //        cterm_keys.push(k);
      }*/
    PTRef getFromCtermMap(SymRef & k);        // { return cterm_map[k]; }

    bool hasBoolKey(PTLKey const & k);
    void addToBoolMap(PTLKey && k, PTRef tr);
    PTRef getFromBoolMap(PTLKey const & k);

    bool hasCplxKey(PTLKey const & k);
    void addToCplxMap(PTLKey && k, PTRef tr);
    PTRef getFromCplxMap(PTLKey const & k);

    PtermIter getPtermIter(); // { return PtermIter(idToPTRef); }

    std::size_t getNumberOfTerms() const { return pta.getNumTerms(); }

private:
    static int const ptstore_buf_idx;
    static int const ptstore_vec_idx;

    PtermAllocator pta{1024 * 1024};
    SymStore & symstore;
    vec<PTRef> idToPTRef;

    Map<SymRef, PTRef, SymRefHash, Equal<SymRef>> cterm_map; // Mapping constant symbols to terms

    std::unordered_map<PTLKey, PTRef, PTLHash, Equal<PTLKey>> cplx_map; // Mapping complex terms to canonical terms

    std::unordered_map<PTLKey, PTRef, PTLHash, Equal<PTLKey>> bool_map; // Mapping boolean terms to canonical terms
};
} // namespace opensmt

#endif
