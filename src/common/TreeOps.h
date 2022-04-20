/*
 * Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef Common_TreeOps_h
#define Common_TreeOps_h


#include "Logic.h"
#include "NatSet.h"
#include "Pterm.h"
#include "Vec.h"

#include <unordered_set>


template<typename TConfig>
class TermVisitor {
    Logic const & logic;
    TConfig & cfg;
public:
    TermVisitor(Logic const & logic, TConfig & cfg) : logic(logic), cfg(cfg) {}

    void visit(PTRef root) {
        // Avoid initializations if no traversal will be done
        if (logic.isVar(root)) {
            if (cfg.previsit(root))
                cfg.visit(root);
            return;
        }
        struct DFSEntry {
            DFSEntry(PTRef term) : term(term) {}
            PTRef term;
            unsigned int nextChild = 0;
        };

        auto termMarks = logic.getTermMarks(logic.getPterm(root).getId());
        std::vector<DFSEntry> toProcess;
        toProcess.emplace_back(root);
        while (not toProcess.empty()) {
            auto & currentEntry = toProcess.back();
            PTRef currentRef = currentEntry.term;
            auto currentId = logic.getPterm(currentRef).getId();
            if (not cfg.previsit(currentRef)) {
                toProcess.pop_back();
                termMarks.mark(currentId);
                continue;
            }
            assert(not termMarks.isMarked(currentId));
            Pterm const & term = logic.getPterm(currentRef);
            unsigned childrenCount = term.size();
            if (currentEntry.nextChild < childrenCount) {
                PTRef nextChild = term[currentEntry.nextChild];
                ++currentEntry.nextChild;
                auto childId = logic.getPterm(nextChild).getId();
                if (not termMarks.isMarked(childId)) {
                    toProcess.push_back(DFSEntry(nextChild));
                }
                continue;
            }
            // If we are here, we have already processed all children
            assert(not termMarks.isMarked(currentId));
            cfg.visit(currentRef);
            termMarks.mark(currentId);
            toProcess.pop_back();
        }
    }
};

class DefaultVisitorConfig {
public:
    virtual bool previsit(PTRef) { return true; } // should continue visiting
    virtual void visit(PTRef) { } // don't do anything
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

class TopLevelConjunctsConfig : public DefaultVisitorConfig {
    Logic const & logic;
    vec<PTRef> & conjuncts;
public:
    TopLevelConjunctsConfig(Logic const & logic, vec<PTRef> & res) : logic(logic), conjuncts(res) {}

    bool previsit(PTRef term) override {
        if (not logic.isAnd(term)) {
            conjuncts.push(term);
            return false;
        }
        return true;
    }
};

inline void topLevelConjuncts(Logic const & logic, PTRef fla, vec<PTRef> & res) {
    TopLevelConjunctsConfig config(logic, res);
    TermVisitor<TopLevelConjunctsConfig>(logic, config).visit(fla);
}

inline vec<PTRef> topLevelConjuncts(Logic const & logic, PTRef fla) {
    vec<PTRef> res;
    topLevelConjuncts(logic, fla, res);
    return res;
}

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
[[deprecated]]
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
[[deprecated]]
void getTermList(PTRef tr, vec<T>& list_out, Logic& logic) {
    getTermsList({tr}, list_out, logic);
}

// Get variables starting from the root
//
[[deprecated("Use variables(Logic &, PTRef) instead.")]]
inline void
getVars(PTRef tr, Logic& logic, MapWithKeys<PTRef,bool,PTRefHash>& vars)
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

template<typename TPred>
class TermCollectorConfig : public DefaultVisitorConfig {
    TPred predicate;
    vec<PTRef> gatheredTerms;
public:
    TermCollectorConfig(TPred predicate) : predicate(std::move(predicate)) {}
    vec<PTRef> && extractCollectedTerms() { return std::move(gatheredTerms); }
    void visit(PTRef term) override { if (predicate(term)) gatheredTerms.push(term); }
};

template<typename TPred>
static vec<PTRef> matchingSubTerms(Logic const & logic, PTRef term, TPred predicate) {
    TermCollectorConfig<TPred> config(predicate);
    TermVisitor<decltype(config)>(logic, config).visit(term);
    return config.extractCollectedTerms();
}

inline vec<PTRef> subTerms(Logic const & logic, PTRef term) {
    return matchingSubTerms(logic, term, [](PTRef) { return true; });
}

/* Returns all variables present in the given term */
inline vec<PTRef> variables(Logic const & logic, PTRef term) {
    return matchingSubTerms(logic, term, [&](PTRef subTerm) { return logic.isVar(subTerm); });
}

#endif
