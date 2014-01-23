#ifndef Common_TreeOps_h
#define Common_TreeOps_h
#include "minisat/mtl/Vec.h"
#include "pterms/Pterm.h"
#include "logics/Logic.h"

template<class T>
void getTermList(PTRef tr, vec<T>& list_out, Logic& logic) {
    vec<PTRef> queue;

    queue.push(tr);
    list_out.push(PtChild(tr, PTRef_Undef, -1));

    while (queue.size() > 0) {
        tr = queue.last();
        queue.pop();
        Pterm& pt = logic.getPterm(tr);
        for (int i = 0; i < pt.size(); i++) {
            queue.push(pt[i]);
            list_out.push(T(pt[i], tr, i));
        }
    }
}
#endif
