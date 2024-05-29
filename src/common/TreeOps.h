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
public:
    TermVisitor(Logic const & logic, TConfig & cfg) : logic(logic), cfg(cfg) {}

    // FIXME: These should be non-virtual, but we need to modify PtermNodeCounter first
    virtual void visit(opensmt::span<const PTRef> roots);
    virtual void visit(PTRef root);

private:
    Logic const & logic;
    TConfig & cfg;
};

template<typename TConfig> void TermVisitor<TConfig>::visit(opensmt::span<const PTRef> roots) {
    struct DFSEntry {
        explicit DFSEntry(PTRef term) : term(term) {}
        PTRef term;
        unsigned int nextChild = 0;
    };

    std::vector<DFSEntry> toProcess;
    toProcess.reserve(roots.size());
    PTId maxId{0};
    for (const PTRef root : roots) {
        toProcess.emplace_back(root);
        auto id = logic.getPterm(root).getId();
        if (id.x > maxId.x) { maxId = id; }
    }
    auto termMarks = logic.getTermMarks(maxId);
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
            if (not termMarks.isMarked(childId)) { toProcess.push_back(DFSEntry(nextChild)); }
            continue;
        }
        // If we are here, we have already processed all children
        assert(not termMarks.isMarked(currentId));
        cfg.visit(currentRef);
        termMarks.mark(currentId);
        toProcess.pop_back();
    }
}
template<typename TConfig> void TermVisitor<TConfig>::visit(PTRef root) {
    // Avoid initializations if no traversal will be done
    if (logic.isVar(root)) {
        if (cfg.previsit(root)) cfg.visit(root);
        return;
    }
    return visit(opensmt::span<const PTRef>(&root, 1));
}

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

class PtermNodeCounterConfig : public DefaultVisitorConfig {
    friend class PtermNodeCounter;
    uint32_t nodeCounter = 0;
    uint32_t maxNodes;
    std::unordered_map<PTRef,uint32_t,PTRefHash> & countLookup;
    using Cache = std::pair<uint32_t, std::unordered_map<PTRef,uint32_t,PTRefHash>>;
public:
    PtermNodeCounterConfig(Cache & cache) : maxNodes(cache.first), countLookup(cache.second) {}
    bool limitReached() const { return nodeCounter >= maxNodes; }
    void visit(PTRef tr) override {
        auto it = countLookup.find(tr);
        if (it != countLookup.end()) {
            if (it->second >= maxNodes) {
                nodeCounter = std::max(nodeCounter, maxNodes);
            }
        } else {
            ++ nodeCounter;
        }
    }
    bool previsit(PTRef tr) override {
        auto it = countLookup.find(tr);
        if (it != countLookup.end() and it->second >= maxNodes) {
            nodeCounter = std::max(nodeCounter, it->second);
        }
        return (nodeCounter < maxNodes);
    }
    uint32_t getCount() const { return nodeCounter; }
};

class PtermNodeCounter : public TermVisitor<PtermNodeCounterConfig> {
    PtermNodeCounterConfig::Cache cache;
    PtermNodeCounterConfig cfg;
public:
    PtermNodeCounter(Logic const & logic, int countUntil) : TermVisitor<PtermNodeCounterConfig>(logic, cfg), cache(countUntil, std::unordered_map<PTRef,uint32_t,PTRefHash>()), cfg(cache) {}
    void visit(PTRef root) override {
        cfg.nodeCounter = 0;
        TermVisitor<PtermNodeCounterConfig>::visit(root);
        if (cache.second.find(root) == cache.second.end()) {
            cache.second.insert({root, getCount()});
        }
    }
    bool limitReached() const { return cfg.limitReached(); }
    uint32_t getCount() const { return cfg.getCount(); }
};
#endif
