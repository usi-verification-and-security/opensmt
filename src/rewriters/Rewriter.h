//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_REWRITER_H
#define OPENSMT_REWRITER_H

#include "Logic.h"

template<typename TConfig, typename TAsgn>
class Rewriter {
    Logic & logic;
    TConfig & cfg;
public:
    Rewriter(Logic & logic, TConfig & cfg) : logic(logic), cfg(cfg) {}

    opensmt::pair<PTRef,Map<PTRef,TAsgn,PTRefHash>> rewrite(PTRef root) {
        struct DFSEntry {
            DFSEntry(PTRef term) : term(term) {}
            PTRef term;
            unsigned int nextChild = 0;
        };
        // MB: Relies on an invariant that id of a child is lower than id of a parent.
        auto size = Idx(logic.getPterm(root).getId()) + 1;
        std::vector<char> done;
        done.resize(size, 0);
        Map<PTRef, TAsgn, PTRefHash> substitutions;
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
            if (cfg.treatIteAsVar() and logic.isIte(term.symb())) {
                childrenCount = 0;
            }
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
            for (auto i = 0; i < newArgs.size(); ++i) {
                TAsgn it;
                bool childChanged = substitutions.peek(term[i], it);
                needsChange |= childChanged;
                newArgs[i] = childChanged ? cfg.getAsgnTerm(it) : term[i];
            }
            PTRef newTerm = needsChange ? logic.insertTerm(term.symb(), newArgs) : currentRef;
            if (needsChange) {
                substitutions.insert(currentRef, TAsgn(newTerm));
            }
            // The reference "term" has now been possibly invalidated! Do not access it anymore!
            PTRef rewritten = cfg.rewrite(newTerm);
            if (rewritten != newTerm) {
                substitutions.insert(currentRef, TAsgn(rewritten));
            }
            done[currentId] = 1;
            toProcess.pop_back();
        }

        TAsgn it;
        PTRef res = substitutions.peek(root, it) ? cfg.getAsgnTerm(it) : root;
        return {res, std::move(substitutions)};
    }
};

template<typename TAsgn>
class DefaultRewriterConfig {
public:
    static bool isEnabled(TAsgn);
    static PTRef getAsgnTerm(TAsgn a);
    static PTRef & getAsgnTermRef(TAsgn & a);
    virtual bool previsit(PTRef term) { return true; } // should continue visiting
    virtual PTRef rewrite(PTRef term) { return term; } // don't do anything
    virtual bool treatIteAsVar() const { return true; }
};

template <typename TAsgn>
class IteRewriterConfig : public DefaultRewriterConfig<TAsgn> {
public:
    virtual bool treatIteAsVar() const override { return false; }
};

class NoOpRewriter : Rewriter<DefaultRewriterConfig<PTRef>,PTRef> {
    DefaultRewriterConfig<PTRef> config;
public:
    NoOpRewriter(Logic & logic) : Rewriter<DefaultRewriterConfig<PTRef>,PTRef>(logic, config) {}
};

#endif //OPENSMT_REWRITER_H