#include "PtStore.h"

PtStore::PtStore(SymStore& symstore_, SStore& sortstore_)
    : symstore(symstore_), sortstore(sortstore_) { }

char* PtStore::printTerm_(PTRef tr) const {
    const Pterm& t = pta[tr];
    SymRef sr = t.symb();
    char* out;
    if (t.size() == 0) {
        asprintf(&out, "%s", symstore.getName(sr));
        return out;
    }
    asprintf(&out, "(%s", symstore.getName(sr));
    if (t.size() > 0) {
        char* old = out;
        asprintf(&out, "%s ", old);
        free(old);
        for (int i = 0; i < t.size(); i++) {
            old = out;
            asprintf(&out, "%s%s", old, printTerm_(t[i]));
            free(old);
            if (i < t.size()-1) {
                old = out;
                asprintf(&out, "%s ", old);
                free(old);
            }
        }
    }
    char* old = out;
    asprintf(&out, "%s)", old);
    free(old);
    return out;
}

//
// Resolves the PTRef for name s taking into account polymorphism
// Creates the term.
// Returns PTRef_Undef if the name is not defined anywhere
//
PTRef PtStore::lookupTerm(const char* s, const vec<PTRef>& args) {
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
                        return insertTerm(ctr, args);
                    }
                }
                // The term might still be one of the special cases:
                // left associative
                // - requires that the left argument and the return value have the same sort
                else if (t.nargs() < args.size_() && t.left_assoc() && symstore[pta[args[0]].symb()].rsort() == t.rsort()) {
                    int j = 1;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[1]) break;
                    }
                    if (j == args.size())
                        return insertTerm(ctr, args);
                }
                else if (t.nargs() < args.size_() && t.right_assoc()) {
                    opensmt_error2("right assoc term not implemented yet", symstore.getName(ctr));
                    return PTRef_Undef;
                }
                else if (t.nargs() < args.size_() && t.chainable()) {
                    opensmt_error2("chainable term not implemented yet", symstore.getName(ctr));
                    return PTRef_Undef;
                }
                else if (t.nargs() < args.size_() && t.pairwise()) {
                    int j = 0;
                    for (; j < args.size(); j++) {
                        SymRef argt = pta[args[j]].symb();
                        if (symstore[argt].rsort() != t[0]) break;
                    }
                    if (j == args.size()) return insertTerm(ctr, args);
                }
                else
                    return PTRef_Undef;
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
                    return insertTerm(ctr, args);
            }
        }
    }
    // Not found
    return PTRef_Undef;
}


char* PtStore::printTerm(PTRef tr) const {
    char* tms = printTerm_(tr);
    return tms;
}
