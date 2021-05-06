//
// Created by Martin Blicha on 04.05.21.
//

#ifndef OPENSMT_DISTINCTREWRITER_H
#define OPENSMT_DISTINCTREWRITER_H

#include "Rewriter.h"

#include <unordered_set>

class DistinctRewriteConfig : public DefaultRewriterConfig {
protected:
    Logic & logic;
public:
    DistinctRewriteConfig(Logic & logic) : logic(logic) {}

    bool previsit(PTRef term) override {
        return logic.hasSortBool(term);
    }

    PTRef rewrite(PTRef ptr) override {
        if (logic.isDisequality(ptr) and doRewriteDistinct(ptr)) {
            Pterm const & term = logic.getPterm(ptr);
            vec<PTRef> args;
            args.capacity(term.nargs());
            for (PTRef arg : term) {
                args.push(arg);
            }
            vec<PTRef> inequalities;
            for (int i = 0; i < args.size(); ++i) {
                for (int j = i + 1; j < args.size(); ++j) {
                    inequalities.push(logic.mkNot(logic.mkEq(args[i], args[j])));
                }
            }
            return logic.mkAnd(inequalities);
        }
        return ptr;
    }

    virtual bool doRewriteDistinct(PTRef dist) const {
        return true;
    }
};


class KeepTopLevelDistinctRewriteConfig : public DistinctRewriteConfig {
public:
    using TopLevelDistincts = std::unordered_set<PTRef, PTRefHash>;
    KeepTopLevelDistinctRewriteConfig(Logic & logic, std::unordered_set<PTRef, PTRefHash> topLevelDistincts):
        DistinctRewriteConfig(logic),
        topLevelDistincts(std::move(topLevelDistincts))
        {}

    bool doRewriteDistinct(PTRef dist) const override {
        return topLevelDistincts.find(dist) == topLevelDistincts.end();
    }
private:
     TopLevelDistincts topLevelDistincts;
};

class DistinctRewriter : public Rewriter<DistinctRewriteConfig> {
    DistinctRewriteConfig config;
public:
    DistinctRewriter(Logic & logic): Rewriter<DistinctRewriteConfig>(logic, config), config(logic) {}
};

class KeepTopLevelDistinctRewriter : public Rewriter<KeepTopLevelDistinctRewriteConfig> {
    KeepTopLevelDistinctRewriteConfig config;
public:
    using TopLevelDistincts = KeepTopLevelDistinctRewriteConfig::TopLevelDistincts;
    KeepTopLevelDistinctRewriter(Logic & logic, TopLevelDistincts topLevelDistincts):
        Rewriter<KeepTopLevelDistinctRewriteConfig>(logic, config),
        config(logic, std::move(topLevelDistincts))
        {}
};


inline PTRef rewriteDistincts(Logic & logic, PTRef fla) {
    return DistinctRewriter(logic).rewrite(fla);
}

PTRef rewriteDistinctsKeepTopLevel(Logic & logic, PTRef fla);



#endif //OPENSMT_DISTINCTREWRITER_H
