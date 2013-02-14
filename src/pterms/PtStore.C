#include "PtStore.h"

PtStore::PtStore(TStore& symstore_, SStore& sortstore_, TRef sym_true, TRef sym_false)
    : symstore(symstore_), sortstore(sortstore_) {
    vec<PTRef> tmp;
    term_true  = insertTerm(sym_true,  tmp);
    term_false = insertTerm(sym_false, tmp);
}

char* PtStore::printTerm_(PTRef tr) const {
    const Pterm& t = pta[tr];
    TRef sr = t.symb();
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

char* PtStore::printTerm(PTRef tr) const {
    char* tms = printTerm_(tr);
    return tms;
}
