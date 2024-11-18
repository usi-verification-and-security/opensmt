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

#include "PtStore.h"

#include <common/ApiException.h>
#include <common/InternalException.h>

#include <algorithm>
#include <cstring>

namespace opensmt {
int const PtStore::ptstore_vec_idx = 1;
int const PtStore::ptstore_buf_idx = 2;

bool PtStore::isAmbiguousNullarySymbolName(std::string_view name) const {
    auto * values = symstore.getRefOrNull(name.data());
    if (not values) { return false; }
    assert(values);
    int matches = 0;
    for (SymRef sr : *values) {
        if (symstore[sr].nargs() == 0) { matches++; }
        if (matches > 1) return true;
    }
    return false;
}

vec<SymRef> PtStore::getHomonymousNullarySymbols(std::string_view name) const {
    auto * values = symstore.getRefOrNull(name.data());
    if (not values) { return {}; }
    vec<SymRef> ambiguousNullarySymbols;
    for (SymRef sr : *values) {
        if (symstore[sr].nargs() == 0) { ambiguousNullarySymbols.push(sr); }
    }
    return ambiguousNullarySymbols;
}

//
// Resolves the SymRef for name s taking into account polymorphism
// Returns SymRef_Undef if the name is not defined anywhere
//
SymRef PtStore::lookupSymbol(char const * s, vec<PTRef> const & args, SymbolMatcher symbolMatcher, SRef sort) {
    auto * values = symstore.getRefOrNull(s);
    std::vector<SymRef> candidates;
    if (values) {
        vec<SymRef> const & trefs = *values;
        if (symstore[trefs[0]].noScoping()) {
            // No need to look forward, this is the only possible term
            // list
            for (int i = 0; i < trefs.size(); i++) {
                SymRef ctr = trefs[i];
                Symbol const & t = symstore[ctr];
                if (t.nargs() == args.size_()) {
                    // t is a potential match.  Check that arguments match
                    uint32_t j = 0;
                    for (; j < t.nargs(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (t[j] != symstore[argt].rsort()) break;
                    }
                    if (j == t.nargs()) {
                        // Add to list of candidates
                        candidates.push_back(ctr);
                    }
                }
                // The term might still be one of the special cases:
                // left associative
                // - requires that the left argument and the return value have the same sort
                else if (t.left_assoc() && symstore[pta[args[0]].symb()].rsort() == t.rsort()) {
                    int j = 1;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[1]) break;
                    }
                    if (j == args.size()) {
                        // We add this candidate only if the return type of the candidate is new.
                        SRef ctrReturnSort = symstore[ctr].rsort();
                        if (not std::any_of(candidates.begin(), candidates.end(), [this, ctrReturnSort](SymRef sr) {
                                return symstore[sr].rsort() == ctrReturnSort;
                            })) {
                            candidates.push_back(ctr);
                        }
                    }
                } else if (t.right_assoc()) {
                    throw InternalException(std::string("right assoc term not implemented yet:") +
                                            symstore.getName(ctr));
                } else if (t.nargs() < args.size_() && t.chainable()) {
                    int j = 0;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[0]) break;
                    }
                    if (j == args.size()) { candidates.push_back(ctr); }
                } else if (t.nargs() < args.size_() && t.pairwise()) {
                    int j = 0;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[0]) break;
                    }
                    if (j == args.size()) { candidates.push_back(ctr); }
                }
            }
        } else {
            for (int i = 0; i < trefs.size(); i++) {
                SymRef ctr = trefs[i];
                Symbol const & t = symstore[ctr];
                if (t.nargs() == args.size_()) {
                    // t is a potential match.  Check that arguments match
                    uint32_t j = 0;
                    for (; j < t.nargs(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (t[j] != symstore[argt].rsort()) break;
                    }
                    if (j == t.nargs()) { candidates.push_back(ctr); }
                }
            }
        }
    }

    auto endOfMatches = std::remove_if(candidates.begin(), candidates.end(), [this, &symbolMatcher](SymRef sr) {
        return not symstore[sr].matches(symbolMatcher);
    });
    candidates.erase(endOfMatches, candidates.end());

    if (candidates.empty()) {
        return SymRef_Undef; // Not found
    } else if (candidates.size() == 1 and sort == SRef_Undef) {
        return candidates[0];
    } else if (candidates.size() == 1 and sort != SRef_Undef) {
        if (symstore[candidates[0]].rsort() != sort) {
            return SymRef_Undef;
        } else {
            return candidates[0];
        }
    } else if (strcmp(s, "*") == 0) {
        assert(candidates.size() == 2);
        return candidates[0];
    }
    assert(candidates.size() > 1);
    if (sort == SRef_Undef) { throw ApiException("Ambiguous symbol: `" + std::string(s) + "'"); }

    assert(sort != SRef_Undef);

    auto equalSortEnd = std::remove_if(candidates.begin(), candidates.end(),
                                       [this, sort](SymRef sr) { return symstore[sr].rsort() != sort; });
    candidates.erase(equalSortEnd, candidates.end());

    if (candidates.empty()) { return SymRef_Undef; }
    if (candidates.size() > 1) {
        throw InternalException("System has " + std::to_string(candidates.size()) +
                                " symbols with same argument and return sorts");
    }

    assert(candidates.size() == 1);
    assert(symstore[candidates[0]].rsort() == sort);
    return candidates[0];
}

PTRef PtermIter::operator*() {
    if (i < idToPTRef.size())
        return idToPTRef[i];
    else
        return PTRef_Undef;
}
PtermIter const & PtermIter::operator++() {
    i++;
    return *this;
}

PTRef PtStore::newTerm(SymRef const sym, vec<PTRef> const & ps) {
    PTRef tr = pta.alloc(sym, ps);
    idToPTRef.push(tr);
    assert(idToPTRef.size_() == pta.getNumTerms());
    return tr;
}

void PtStore::free(PTRef r) {
    pta.free(r);
} // this is guaranteed to be lazy

Pterm & PtStore::operator[](PTRef tr) {
    return pta[tr];
}
Pterm const & PtStore::operator[](PTRef tr) const {
    return pta[tr];
}

bool PtStore::hasCtermKey(SymRef & k) {
    return cterm_map.has(k);
}
void PtStore::addToCtermMap(SymRef & k, PTRef tr) {
    cterm_map.insert(k, tr);
}
PTRef PtStore::getFromCtermMap(SymRef & k) {
    return cterm_map[k];
}

bool PtStore::hasBoolKey(PTLKey const & k) {
    return bool_map.find(k) != bool_map.end();
}
void PtStore::addToBoolMap(PTLKey && k, PTRef tr) {
    bool_map[std::move(k)] = tr;
}
PTRef PtStore::getFromBoolMap(PTLKey const & k) {
    return bool_map.at(k);
}

bool PtStore::hasCplxKey(PTLKey const & k) {
    return cplx_map.find(k) != cplx_map.end();
}
void PtStore::addToCplxMap(PTLKey && k, PTRef tr) {
    cplx_map[std::move(k)] = tr;
}
PTRef PtStore::getFromCplxMap(PTLKey const & k) {
    return cplx_map.at(k);
}

PtermIter PtStore::getPtermIter() {
    return PtermIter(idToPTRef);
}
} // namespace opensmt
