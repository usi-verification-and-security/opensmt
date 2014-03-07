#ifndef Common_TreeOps_h
#define Common_TreeOps_h
#include "minisat/mtl/Vec.h"
#include "pterms/Pterm.h"
#include "logics/Logic.h"

template<class T>
class Qel {
  public:
    T x;
    int chk;
    Qel(T r) : x(r), chk(0) {};
};

//
// Visit the term tree rooted at tr.  Return in list_out every term occurrence
// in the tree in an order where the parent term is always listed before its
// children.  Also store the information who is the parent of the term.  Since
// the parent info is also returned, duplicate terms will be reported.
// However, the list_out will not contain duplicates.
//
template<class T>
void getTermList(PTRef tr, vec<T>& list_out, Logic& logic) {
    vec<Qel<PtChild> > queue;
    Map<PtChild,bool,PtChildHash> seen;
    Map<PTRef,int,PTRefHash> chkd;

    queue.push(Qel<PtChild>(PtChild(tr, PTRef_Undef, -1)));

    while (queue.size() > 0) {
        Qel<PtChild> qtr = queue.last();
        Pterm& pt = logic.getPterm(qtr.x.tr);
        int i = qtr.chk;
        if (i < pt.size()) {
            PtChild ptc(pt[i], qtr.x.tr, i);
            if (!seen.contains(ptc))
                queue.push(Qel<PtChild>(ptc));
            qtr.chk = i+1;
        } else {
            T ptc(qtr.x.tr, qtr.x.parent, qtr.x.pos);
            list_out.push(ptc);
            seen.insert(ptc, true);
            assert(queue.size() > 0);
            queue.pop();
        }
    }
}
#endif
