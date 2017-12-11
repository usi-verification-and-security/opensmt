#include "BindedRows.h"

void
BindedRowsStore::remove(LVRef v, LVRef target) {
    OccListRef br = lva[target].getBindedRowsRef();
    BindedRows &b = bra[br];
    printf("Binded rows: Before removal of %s from %s\n", logic.printTerm(lva[v].getPTRef()), logic.printTerm(lva[target].getPTRef()));
    for (int i = 0; i < bra[br].rows.size(); i++) {
        printf("  Var %s, pos %d\n", logic.printTerm(lva[bra[br].rows[i].var].getPTRef()), bra[br].rows[i].pos);
    }
    b.remove(v);
    printf("Binded rows: After removal of %s\n", logic.printTerm(lva[v].getPTRef()));
    for (int i = 0; i < bra[br].rows.size(); i++) {
        printf("  Var %s, pos %d\n", logic.printTerm(lva[bra[br].rows[i].var].getPTRef()), bra[br].rows[i].pos);
    }
}

void
BindedRowsStore::add(LVRef v, int pos, LVRef target) {
//    printf("Binded rows: debug count %d\n", debug_count++);
    BindedRows& r = bra[lva[target].getBindedRowsRef()];
//    printf("Binded rows: Before addition of %s to %s\n", logic.printTerm(lva[v].getPTRef()), logic.printTerm(lva[target].getPTRef()));
//    for (int i = 0; i < r.rows.size(); i++) {
//        printf("  Var %s, pos %d\n", logic.printTerm(lva[r.rows[i].var].getPTRef()), r.rows[i].pos);
//    }
    bra[lva[target].getBindedRowsRef()].add(v, pos);
 //   printf("Binded rows: After addition of %s\n", logic.printTerm(lva[v].getPTRef()));
//    for (int i = 0; i < r.rows.size(); i++) {
//        printf("  Var %s, pos %d\n", logic.printTerm(lva[r.rows[i].var].getPTRef()), r.rows[i].pos);
//    }
}

void
BindedRows::remove(LVRef v)
{

    for (int i = varToIdx[v]+1; i < rows.size(); i++) {
        assert(i > 0);
        rows[i-1] = rows[i];
        varToIdx[rows[i-1].var] = i-1;
    }
    rows.shrink(1);
    varToIdx.remove(v);
}

