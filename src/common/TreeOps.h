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

#include <unordered_set>
#include "Vec.h"
#include "Pterm.h"
#include "Logic.h"


template<typename TConfig>
class TermVisitor {
    Logic & logic;
    TConfig & cfg;
public:
    TermVisitor(Logic & logic, TConfig & cfg) : logic(logic), cfg(cfg) {}

    void visit(PTRef root) {
        struct DFSEntry {
            DFSEntry(PTRef term) : term(term) {}
            PTRef term;
            unsigned int nextChild = 0;
        };
        // MB: Relies on an invariant that id of a child is lower than id of a parent.
        auto size = Idx(logic.getPterm(root).getId()) + 1;
        std::vector<char> done;
        done.resize(size, 0);
        std::vector<DFSEntry> toProcess;
        toProcess.emplace_back(root);
        while (not toProcess.empty()) {
            auto & currentEntry = toProcess.back();
            PTRef currentRef = currentEntry.term;
            if (not cfg.previsit(currentRef)) {
                toProcess.pop_back();
                continue;
            }
            assert(not done[Idx(logic.getPterm(currentRef).getId())]);
            Pterm const & term = logic.getPterm(currentRef);
            unsigned childrenCount = term.size();
            if (currentEntry.nextChild < childrenCount) {
                PTRef nextChild = term[currentEntry.nextChild];
                ++currentEntry.nextChild;
                if (not done[Idx(logic.getPterm(nextChild).getId())]) {
                    toProcess.push_back(DFSEntry(nextChild));
                }
                continue;
            }
            // If we are here, we have already processed all children
            assert(done[Idx(term.getId())] == 0);
            cfg.visit(currentRef);
            done[Idx(logic.getPterm(currentRef).getId())] = 1;
            toProcess.pop_back();
        }
    }
};

class DefaultVisitorConfig {
public:
    virtual bool previsit(PTRef term) { return true; } // should continue visiting
    virtual void visit(PTRef term) { } // don't do anything
};

class AppearsInUFVisitorConfig : public DefaultVisitorConfig {
    Logic & logic;
public:
    AppearsInUFVisitorConfig(Logic & logic): logic(logic) {}

    void visit(PTRef term) override {
        if (logic.isUF(term)) {
            for (PTRef child : logic.getPterm(term)) {
                if (logic.hasSortBool(child)) {
                    logic.setAppearsInUF(logic.isNot(child) ? logic.getPterm(child)[0] : child);
                }
            }
        }
    }
};

class AppearsInUfVisitor : public TermVisitor<AppearsInUFVisitorConfig> {
    AppearsInUFVisitorConfig cfg;
public:
    AppearsInUfVisitor(Logic & logic): TermVisitor<AppearsInUFVisitorConfig>(logic, cfg), cfg(logic) {}
};

template<class T>
class Qel {
  public:
    T x;
    int chk;
    Qel(T r) : x(r), chk(0) {};
};

//
// Visit the term dag starting from vec<PTRef> trs.  Return in list_out every term occurrence
// in the tree in an order where the parent term is always listed before its
// children.  Also store the information who is the parent of the term.  Since
// the parent info is also returned, duplicate terms will be reported.
// However, the list_out will not contain duplicates.
//
template<class T>
void getTermsList(const vec<PTRef>& trs, vec<T>& list_out, Logic& logic) {
    vec<Qel<PtChild> > queue;
    Map<PtChild,bool,PtChildHash> seen;
    Map<PTRef,int,PTRefHash> chkd;

#ifdef PEDANTIC_DEBUG
//    assert(logic.hasSym(logic.getPterm(tr).symb()));
#endif
    for (int i = 0; i < trs.size(); i++)
        queue.push(Qel<PtChild>(PtChild(trs[i], PTRef_Undef, -1)));

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

template<class T>
void getTermList(PTRef tr, vec<T>& list_out, Logic& logic) {
    getTermsList({tr}, list_out, logic);
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

inline std::vector<PTRef>
getAtoms(PTRef tr, Logic & logic)
{
    std::vector<PTRef> atoms;
    std::unordered_set<PTRef, PTRefHash> seen;
    std::vector<PTRef> queue;
    queue.push_back(tr);
    while (queue.size() != 0)
    {
        tr = queue.back();
        if (seen.find(tr) != seen.end()) {
            queue.pop_back();
            continue;
        }

        if (logic.isBooleanOperator(tr)) { // I only need to consider children of connectives, no need for going further
            bool unprocessed_children = false;
            for (int i = 0; i < logic.getPterm(tr).size(); i++)
            {
                PTRef c = logic.getPterm(tr)[i];
                if (seen.find(c) != seen.end()) continue;
                else {
                    queue.push_back(c);
                    unprocessed_children = true;
                }
            }
            if (unprocessed_children == true) continue;
        } // if not boolean operator => it is an atom!
        queue.pop_back();
        assert(logic.isBooleanOperator(tr) || logic.hasSortBool(tr)); // MB: we should not go past atoms!
        if (!logic.isBooleanOperator(tr) && logic.hasSortBool(tr)) {
            atoms.push_back(tr);
        }
        seen.insert(tr);
    }
    return atoms;
}

#endif
