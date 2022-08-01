/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SUBSTITUTOR_H
#define OPENSMT_SUBSTITUTOR_H

#include "Rewriter.h"

class SubstitutionConfig : public DefaultRewriterConfig {
public:
    using SubMap = Logic::SubstMap;

private:
    SubMap const & subMap;

public:
    SubstitutionConfig(SubMap const & subMap) : subMap(subMap) {}
    PTRef rewrite(PTRef term) override {
        PTRef result;
        return subMap.peek(term, result) ? result : term;
    }
};

class Substitutor : public Rewriter<SubstitutionConfig> {
    SubstitutionConfig config;

public:
    Substitutor(Logic & logic, SubstitutionConfig::SubMap const & substs)
        : Rewriter<SubstitutionConfig>(logic, config), config(substs) {}
};

#endif // OPENSMT_SUBSTITUTOR_H