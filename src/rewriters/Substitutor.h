//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_SUBSTITUTOR_H
#define OPENSMT_SUBSTITUTOR_H

#endif //OPENSMT_SUBSTITUTOR_H

#include "Rewriter.h"

class SubstitutionConfig : public DefaultRewriterConfig {
public:
    using SubMap = Logic::SubstMap;
private:
    SubMap const & subMap;

public:

    SubstitutionConfig(Logic &, SubMap const & subMap): subMap(subMap) {}
    PTRef rewrite(PTRef term) override {
        PTRef result;
        return subMap.peek(term, result) ? result : term;
    }
};

class IteSubstitutionConfig : public IteRewriterConfig {
private:
    using SubMap = Logic::SubstMap;
    SubMap const & subMap;

public:

    IteSubstitutionConfig(Logic &, SubMap const & subMap): subMap(subMap) {}
    PTRef rewrite(PTRef term) override {
        PTRef result = term;
        if (subMap.has(term)) {
            result = subMap[term];
        }
        return result;
    }
};

class Substitutor : public Rewriter<SubstitutionConfig> {
    SubstitutionConfig config;

public:
    Substitutor(Logic &logic, SubstitutionConfig::SubMap const &substs) :
            Rewriter<SubstitutionConfig>(logic, config),
            config(logic, substs) {}
};

class IteSubstitutor : public Rewriter<IteSubstitutionConfig> {
    IteSubstitutionConfig config;

public:
    IteSubstitutor(Logic &logic, MapWithKeys<PTRef, PTRef, PTRefHash> const &substs) :
            Rewriter<IteSubstitutionConfig>(logic, config),
            config(logic, substs) {}
};