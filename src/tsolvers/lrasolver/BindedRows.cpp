#include "BindedRows.h"

void
BindedRowsStore::remove(PolyRef pr, LVRef target) {
    OccListRef br = lva[target].getBindedRowsRef();
    BindedRows &b = bra[br];
    b.remove(pr);
}

void
BindedRowsStore::add(PolyRef row, int pos, LVRef target) {
//    printf("Binded rows: debug count %d\n", debug_count++);
    BindedRows& r = bra[lva[target].getBindedRowsRef()];
//    printf("Binded rows: Before addition of %s to %s\n", logic.printTerm(lva[v].getPTRef()), logic.printTerm(lva[target].getPTRef()));
//    for (int i = 0; i < r.rows.size(); i++) {
//        printf("  Var %s, pos %d\n", logic.printTerm(lva[r.rows[i].var].getPTRef()), r.rows[i].pos);
//    }
    bra[lva[target].getBindedRowsRef()].add(row, pos);
//    printf("Binded rows: After addition of %s\n", logic.printTerm(lva[v].getPTRef()));
//    for (int i = 0; i < r.rows.size(); i++) {
//        printf("  Var %s, pos %d\n", logic.printTerm(lva[r.rows[i].var].getPTRef()), r.rows[i].pos);
//    }
}

void
BindedRows::remove(PolyRef pr)
{
    for (int i = polyToIdx[pr]+1; i < rows.size(); i++) {
        assert(i > 0);
        rows[i-1] = rows[i];
        polyToIdx[rows[i-1].poly] = i-1;
    }
    rows.shrink(1);
    polyToIdx.remove(pr);
}

