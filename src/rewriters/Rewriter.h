//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_REWRITER_H
#define OPENSMT_REWRITER_H

#include "Logic.h"

template<typename TConfig>
class Rewriter {
    Logic & logic;
    TConfig & cfg;
public:
    Rewriter(Logic & logic, TConfig & cfg) : logic(logic), cfg(cfg) {}

    PTRef rewrite(PTRef root) {
        struct DFSEntry {
            DFSEntry(PTRef term) : term(term) {}
            PTRef term;
            unsigned int nextChild = 0;
        };
        // MB: Relies on an invariant that id of a child is lower than id of a parent.
        auto size = Idx(logic.getPterm(root).getId()) + 1;
        std::vector<char> done;
        done.resize(size, 0);
        Map<PTRef, PTRef, PTRefHash> substitutions;
        std::vector<DFSEntry> toProcess;
        toProcess.emplace_back(root);
        while (not toProcess.empty()) {
            auto & currentEntry = toProcess.back();
            PTRef currentRef = currentEntry.term;
            auto currentId = Idx(logic.getPterm(currentRef).getId());
            if (not cfg.previsit(currentRef)) {
                toProcess.pop_back();
                done[currentId] = 1;
                continue;
            }
            assert(not done[currentId]);
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
            vec<PTRef> newArgs(childrenCount);
            bool needsChange = false;
            for (unsigned i = 0; i < childrenCount; ++i) {
                PTRef target;
                bool childChanged = substitutions.peek(term[i], target);
                needsChange |= childChanged;
                newArgs[i] = childChanged ? target : term[i];
            }
            PTRef newTerm = needsChange ? logic.insertTerm(term.symb(), newArgs) : currentRef;
            if (needsChange) {
                substitutions.insert(currentRef, newTerm);
            }
            // The reference "term" has now been possibly invalidated! Do not access it anymore!
            PTRef rewritten = cfg.rewrite(newTerm);
            if (rewritten != newTerm) {
                substitutions.insert(currentRef, rewritten);
            }
            done[currentId] = 1;
            toProcess.pop_back();
        }

        PTRef target;
        PTRef res = substitutions.peek(root, target) ? target : root;
        return res;
    }
};

class DefaultRewriterConfig {
public:
    virtual bool previsit(PTRef term) { return true; } // should continue visiting
    virtual PTRef rewrite(PTRef term) { return term; } // don't do anything
    virtual bool treatIteAsVar() const { return true; }
};

class IteRewriterConfig : public DefaultRewriterConfig {
public:
    virtual bool treatIteAsVar() const override { return false; }
};

class NoOpRewriter : Rewriter<DefaultRewriterConfig> {
    DefaultRewriterConfig config;
public:
    NoOpRewriter(Logic & logic) : Rewriter<DefaultRewriterConfig>(logic, config) {}
};

#endif //OPENSMT_REWRITER_H