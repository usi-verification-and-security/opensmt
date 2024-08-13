/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_DISTINCTREWRITER_H
#define OPENSMT_DISTINCTREWRITER_H

#include "Rewriter.h"

#include <unordered_set>

namespace opensmt {
class DistinctRewriteConfig : public DefaultRewriterConfig {
public:
    DistinctRewriteConfig(Logic & logic) : logic(logic) {}

    bool previsit(PTRef term) override { return logic.hasSortBool(term); }

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
            return logic.mkAnd(std::move(inequalities));
        }
        return ptr;
    }

    virtual bool doRewriteDistinct(PTRef) const { return true; }

protected:
    Logic & logic;
};

class KeepTopLevelDistinctRewriteConfig : public DistinctRewriteConfig {
public:
    using TopLevelDistincts = std::unordered_set<PTRef, PTRefHash>;
    KeepTopLevelDistinctRewriteConfig(Logic & logic, std::unordered_set<PTRef, PTRefHash> topLevelDistincts)
        : DistinctRewriteConfig(logic),
          topLevelDistincts(std::move(topLevelDistincts)) {}

    bool doRewriteDistinct(PTRef dist) const override {
        return topLevelDistincts.find(dist) == topLevelDistincts.end();
    }

private:
    TopLevelDistincts topLevelDistincts;
};

class DistinctRewriter : public Rewriter<DistinctRewriteConfig> {
public:
    DistinctRewriter(Logic & logic) : Rewriter<DistinctRewriteConfig>(logic, config), config(logic) {}

private:
    DistinctRewriteConfig config;
};

class KeepTopLevelDistinctRewriter : public Rewriter<KeepTopLevelDistinctRewriteConfig> {
public:
    using TopLevelDistincts = KeepTopLevelDistinctRewriteConfig::TopLevelDistincts;
    KeepTopLevelDistinctRewriter(Logic & logic, TopLevelDistincts topLevelDistincts)
        : Rewriter<KeepTopLevelDistinctRewriteConfig>(logic, config),
          config(logic, std::move(topLevelDistincts)) {}

private:
    KeepTopLevelDistinctRewriteConfig config;
};
} // namespace opensmt

#endif // OPENSMT_DISTINCTREWRITER_H
