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

#include <sstream>

const int PtStore::ptstore_vec_idx = 1;
const int PtStore::ptstore_buf_idx = 2;

PtStore::PtStore(SymStore& symstore_, SStore& sortstore_)
    : symstore(symstore_), sortstore(sortstore_) { }

//
// Resolves the SymRef for name s taking into account polymorphism
// Returns SymRef_Undef if the name is not defined anywhere
//
SymRef PtStore::lookupSymbol(const char* s, const vec<PTRef>& args) {
    if (symstore.contains(s)) {
        const vec<SymRef>& trefs = symstore.nameToRef(s);
        if (symstore[trefs[0]].noScoping()) {
            // No need to look forward, this is the only possible term
            // list
            for (int i = 0; i < trefs.size(); i++) {
                SymRef ctr = trefs[i];
                const Symbol& t = symstore[ctr];
                if (t.nargs() == args.size_()) {
                    // t is a potential match.  Check that arguments match
                    uint32_t j = 0;
                    for (; j < t.nargs(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (t[j] != symstore[argt].rsort()) break;
                    }
                    if (j == t.nargs()) {
                        // Create / lookup the proper term and return the reference
                        return ctr;
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
                    if (j == args.size())
                        return ctr;
                }
                else if (t.right_assoc()) {
                    opensmt_error2("right assoc term not implemented yet:", symstore.getName(ctr));
                    return SymRef_Undef;
                }
                else if (t.nargs() < args.size_() && t.chainable()) {
                    int j = 0;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[0]) break;
                    }
                    if (j == args.size()) return ctr;
                }
                else if (t.nargs() < args.size_() && t.pairwise()) {
                    int j = 0;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[0]) break;
                    }
                    if (j == args.size()) return ctr;
                }
                else
                    return SymRef_Undef;
            }
        }
    }

    // We get here if it was not in let branches either
    if (symstore.contains(s)) {
        const vec<SymRef>& trefs = symstore.nameToRef(s);
        for (int i = 0; i < trefs.size(); i++) {
            SymRef ctr = trefs[i];
            const Symbol& t = symstore[ctr];
            if (t.nargs() == args.size_()) {
                // t is a potential match.  Check that arguments match
                uint32_t j = 0;
                for (; j < t.nargs(); j++) {
                    SymRef argt = pta[args[j]].symb();
                    if (t[j] != symstore[argt].rsort()) break;
                }
                if (j == t.nargs())
                    return ctr;
            }
        }
    }
    // Not found
    return SymRef_Undef;
}


#ifdef PRODUCE_PROOF
void
PtStore::assignPartition(unsigned int n, PTRef ptr) {
    assert(n >= 0);
    ipartitions_t p = 0;
    setbit(p, n);
    addIPartitions(ptr, p);
}

ipartitions_t&
PtStore::getIPartitions(PTRef _t)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return term_partitions[_t];
//    if(!term_partitions.has(_t)) {
//        ipartitions_t *p_new = new ipartitions_t(0);
//        term_partitions.insert(_t, p_new);
//    }
//    return *(term_partitions[_t]);
}

void
PtStore::setIPartitions(PTRef _t, const ipartitions_t& _p)
{
    term_partitions[_t] = _p;
//    ipartitions_t* new_p = new ipartitions_t(_p);
//    term_partitions.insert(_t, new_p);
}

void
PtStore::addIPartitions(PTRef _t, const ipartitions_t& _p)
{
    term_partitions[_t] |= _p;
//    if (!term_partitions.has(_t)) {
//        ipartitions_t* new_p = new ipartitions_t(0);
//        term_partitions.insert(_t, new_p);
//    }
//    *(term_partitions[_t]) |= _p;
}

ipartitions_t&
PtStore::getIPartitions(SymRef _s)
{
    // MB: // this default construct the value if the key was not present and it is default constructed to 0
    return sym_partitions[_s];
//    if(!sym_partitions.has(_s)) {
//        ipartitions_t* new_p = new ipartitions_t(0);
//        sym_partitions.insert(_s, new_p);
//    }
//    return *(sym_partitions[_s]);
}

void
PtStore::setIPartitions(SymRef _s, const ipartitions_t& _p)
{
    sym_partitions[_s] = _p;
//    assert(!sym_partitions.has(_s));
//    ipartitions_t* p_new = new ipartitions_t(_p);
//    sym_partitions.insert(_s, p_new);
}

void
PtStore::addIPartitions(SymRef _s, const ipartitions_t& _p)
{
    sym_partitions[_s] |= _p;
//    if (!sym_partitions.has(_s)) {
//        ipartitions_t* p_new = new ipartitions_t(0);
//        sym_partitions.insert(_s, p_new);
//    }
//    *(sym_partitions[_s]) |= _p;
}

#endif


PTRef PtermIter::operator* () {
    if (i < idToPTRef.size())
        return idToPTRef[i];
    else
        return PTRef_Undef;
}
const PtermIter& PtermIter::operator++ () { i++; return *this; }


PTRef PtStore::newTerm(const SymRef sym, const vec<PTRef>& ps) {
    PTRef tr = pta.alloc(sym, ps); idToPTRef.push(tr);
    assert(idToPTRef.size() == pta.getNumTerms());
    return tr;
}

void   PtStore::free(PTRef r) { pta.free(r); }  // this is guaranteed to be lazy



Pterm& PtStore::operator[] (PTRef tr) { return pta[tr]; }
const Pterm& PtStore::operator[] (PTRef tr) const { return pta[tr]; }

bool PtStore::hasCtermKey(SymRef& k) { return cterm_map.has(k); }
void PtStore::addToCtermMap(SymRef& k, PTRef tr) {
    cterm_map.insert(k, tr);
//        cterm_keys.push(k);
}
PTRef PtStore::getFromCtermMap(SymRef& k) { return cterm_map[k]; }

bool PtStore::hasBoolKey(PTLKey& k) { return bool_map.has(k); }
void PtStore::addToBoolMap(PTLKey& k, PTRef tr) {
    bool_map.insert(k, tr);
//        bool_keys.push(k);
}
PTRef PtStore::getFromBoolMap(PTLKey& k) { return bool_map[k]; }

bool PtStore::hasCplxKey(PTLKey& k) { return cplx_map.has(k); }
void PtStore::addToCplxMap(PTLKey& k, PTRef tr) {
    cplx_map.insert(k, tr);
//        cplx_keys.push(k);
}
PTRef PtStore::getFromCplxMap(PTLKey& k) { return cplx_map[k]; }

PtermIter PtStore::getPtermIter() { return PtermIter(idToPTRef); }

