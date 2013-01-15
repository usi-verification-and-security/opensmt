#include "PtStore.h"

PtStore::PtStore(TStore& symstore_, SStore& sortstore_, TRef sym_true, TRef sym_false)
    : symstore(symstore_), sortstore(sortstore_) {
    vec<PTRef> tmp;
    term_true  = insertTerm(sym_true,  tmp);
    term_false = insertTerm(sym_false, tmp);
}
