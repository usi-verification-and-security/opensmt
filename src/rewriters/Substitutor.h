/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SUBSTITUTOR_H
#define OPENSMT_SUBSTITUTOR_H

#include "Rewriter.h"

namespace opensmt {
class SubstitutionConfig : public DefaultRewriterConfig {
public:
    using SubMap = Logic::SubstMap;

    SubstitutionConfig(SubMap const & subMap) : subMap(subMap) {}
    PTRef rewrite(PTRef term) override {
        PTRef result;
        return subMap.peek(term, result) ? result : term;
    }

private:
    SubMap const & subMap;
};

class Substitutor : public Rewriter<SubstitutionConfig> {
public:
    Substitutor(Logic & logic, SubstitutionConfig::SubMap const & substs)
        : Rewriter<SubstitutionConfig>(logic, config),
          config(substs) {}

private:
    SubstitutionConfig config;
};
} // namespace opensmt

#endif // OPENSMT_SUBSTITUTOR_H
