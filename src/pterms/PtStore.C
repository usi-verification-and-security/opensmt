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

const int PtStore::ptstore_buf_idx = 1;

PtStore::PtStore(SymStore& symstore_, SStore& sortstore_)
    : symstore(symstore_), sortstore(sortstore_) { }

char* PtStore::printTerm_(PTRef tr, bool ext) const {
    const Pterm& t = pta[tr];
    SymRef sr = t.symb();
    char* out;
    if (t.size() == 0) {
        if (ext)
            asprintf(&out, "%s <%d>", symstore.getName(sr), tr.x);
        else
            asprintf(&out, "%s", symstore.getName(sr));
        return out;
    }

    char* old;
    asprintf(&out, "(%s ", symstore.getName(sr));
    for (int i = 0; i < t.size(); i++) {
        old = out;
        asprintf(&out, "%s%s", old, printTerm_(t[i], ext));
        ::free(old);
        if (i < t.size()-1) {
            old = out;
            asprintf(&out, "%s ", old);
            ::free(old);
        }
    }
    old = out;
    if (ext)
        asprintf(&out, "%s) <%d>", old, tr.x);
    else
        asprintf(&out, "%s)", old);
    ::free(old);
    return out;
}

//
// Resolves the PTRef for name s taking into account polymorphism
// Creates the term.
// Returns PTRef_Undef if the name is not defined anywhere
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
                    opensmt_error2("right assoc term not implemented yet", symstore.getName(ctr));
                    return SymRef_Undef;
                }
                else if (t.nargs() < args.size_() && t.chainable()) {
                    opensmt_error2("chainable term not implemented yet", symstore.getName(ctr));
                    return SymRef_Undef;
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


char* PtStore::printTerm(PTRef tr, bool ext) const
{
    char* tms = printTerm_(tr, ext);
    return tms;
}

int* PtStore::serializeTerms()
{
    int* ptstore_buf = pta.serialize();
    int ptstore_buf_sz = ptstore_buf[0];
    int buf_sz = ptstore_buf_sz+2;
    int* buf = (int*)malloc(buf_sz*sizeof(int));
    buf[0] = buf_sz;
    int ptstore_buf_offs = ptstore_buf_idx+1;
    buf[ptstore_buf_idx] = ptstore_buf_offs;
    for (int i = 0; i < ptstore_buf_sz; i++)
        buf[ptstore_buf_offs+i] = ptstore_buf[i];
    return buf;
}

void PtStore::deserializeTerms(int* buf)
{
    int* ptstore_buf = &buf[buf[ptstore_buf_idx]];
    pta.deserialize(ptstore_buf);
}
