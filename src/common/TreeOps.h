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


#ifndef Common_TreeOps_h
#define Common_TreeOps_h
#include "Vec.h"
#include "Pterm.h"
#include "Logic.h"


class Logic;

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

#ifdef PEDANTIC_DEBUG
//    assert(logic.hasSym(logic.getPterm(tr).symb()));
#endif
    queue.push(Qel<PtChild>(PtChild(tr, PTRef_Undef, -1)));

    while (queue.size() > 0) {
        int q_idx = queue.size() - 1;
#ifdef PEDANTIC_DEBUG
//        assert(logic.hasSym(logic.getPterm(queue[q_idx].x.tr).symb()));
#endif
        Pterm& pt = logic.getPterm(queue[q_idx].x.tr);
        int i = queue[q_idx].chk;
        if (i < pt.size()) {
            PtChild ptc(pt[i], queue[q_idx].x.tr, i);
            if (!seen.has(ptc)) {
                queue.push(Qel<PtChild>(ptc));
#ifdef PEDANTIC_DEBUG
//                assert(logic.hasSym(logic.getPterm(ptc.tr).symb()));
#endif
            }
            queue[q_idx].chk = i+1;
        } else {
            T ptc(queue[q_idx].x.tr, queue[q_idx].x.parent, queue[q_idx].x.pos);
            list_out.push(ptc);
            seen.insert(ptc, true);
            assert(queue.size() > 0);
            queue.pop();
        }
    }
}

// Get variables starting from the root
//
inline void
getVars(PTRef tr, Logic& logic, Map<PTRef,bool,PTRefHash>& vars)
{
    Map<PTRef,bool,PTRefHash> seen;

    vec<PTRef> queue;
    queue.push(tr);
    while (queue.size() != 0)
    {
        tr = queue.last();
        if (seen.has(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        for (int i = 0; i < logic.getPterm(tr).size(); i++)
        {
            PTRef c = logic.getPterm(tr)[i];
            if (seen.has(c)) continue;
            else {
                queue.push(c);
                unprocessed_children = true;
            }
        }
        if (unprocessed_children == true) continue;
        queue.pop();
        if (logic.isVar(tr))
            vars.insert(tr, true);
        seen.insert(tr, true);
    }
    return;
}

#endif
