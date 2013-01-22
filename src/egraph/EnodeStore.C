#include "EnodeStore.h"
#include "Term.h"

ERef EnodeStore::addSymb(TRef t) {
    return ea.alloc(t);
}

ERef EnodeStore::addTerm(ERef sr) {
    return ea.alloc(sr, ERef_Nil, Enode::et_term);
}

ERef EnodeStore::cons(ERef x, ERef y) {
    return ea.alloc(x, y, Enode::et_list);
}


