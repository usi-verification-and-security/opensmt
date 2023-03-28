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

#include "SStore.h"

#include <string>
#include <sstream>

bool SStore::peek(SortSymbol const & symbol, SSymRef & outRef) {
    auto it = this->sortSymbolTable.find(symbol.name);
    if (it != sortSymbolTable.end()) {
        outRef = it->second;
        return true;
    }
    return false;
}

SSymRef SStore::newSortSymbol(SortSymbol symbol) {
    SSymRef res;
    assert(not peek(symbol, res));
    res = ssa.alloc(symbol);
    sortSymbolTable.insert({std::move(symbol.name), res});
    sortSymbols.push(res);
    return res;
}

opensmt::pair<SRef,bool> SStore::getOrCreateSort(SSymRef symbolRef, vec<SRef> && rest)
{
    SortKey key(symbolRef, std::move(rest));
    auto it = sortTable.find(key);
    if (it != sortTable.end()) {
        return {it->second, false};
    }

    SRef sr = sa.alloc(key);
    sorts.push(sr);
    auto emplaceRes = sortTable.emplace(std::move(key), sr);
    assert(emplaceRes.second); (void)emplaceRes;
    return {sr, true};
}


void SStore::copyTo(SStore& other) const {
    other.sa = sa;
    other.ssa = ssa;
//    sorts.copyTo(other.sorts);
    sortSymbols.copyTo(other.sortSymbols);
    other.sortSymbolTable = sortSymbolTable;
    for(auto& it: sortTable){
        SRef sr = other.sa.alloc(it.first);
        other.sorts.push(sr);
        other.sortTable.emplace(it.first, sr);
    }
//    other.sortTable = sortTable;
};