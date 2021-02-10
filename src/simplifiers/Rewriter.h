//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_REWRITER_H
#define OPENSMT_REWRITER_H

#endif //OPENSMT_REWRITER_H

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
        std::unordered_map<PTRef, PTRef, PTRefHash> substitutions;
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
            vec<PTRef> newArgs(childrenCount);
            bool needsChange = false;
            for (unsigned i = 0; i < childrenCount; ++i) {
                auto it = substitutions.find(term[i]);
                bool childChanged = it != substitutions.end();
                needsChange |= childChanged;
                newArgs[i] = childChanged ? it->second : term[i];
            }
            PTRef newTerm = needsChange ? logic.insertTerm(term.symb(), newArgs) : currentRef;
            if (needsChange) {
                substitutions.insert({currentRef, newTerm});
            }
            // The reference "term" has now been possibly invalidated! Do not access it anymore!
            PTRef rewritten = cfg.rewrite(newTerm);
            if (rewritten != newTerm) {
                substitutions[currentRef] = rewritten;
            }
            done[Idx(logic.getPterm(currentRef).getId())] = 1;
            toProcess.pop_back();
        }

        auto it = substitutions.find(root);
        PTRef res = it == substitutions.end() ? root : it->second;
        return res;
    }
};

class DefaultRewriterConfig {
public:
    virtual bool previsit(PTRef term) { return true; } // should continue visiting
    virtual PTRef rewrite(PTRef term) { return term; } // don't do anything
};

class NoOpRewriter : Rewriter<DefaultRewriterConfig> {
    DefaultRewriterConfig config;
public:
    NoOpRewriter(Logic & logic) : Rewriter<DefaultRewriterConfig>(logic, config) {}
};