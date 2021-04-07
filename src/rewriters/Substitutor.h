//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_SUBSTITUTOR_H
#define OPENSMT_SUBSTITUTOR_H

#endif //OPENSMT_SUBSTITUTOR_H

#include "Rewriter.h"

class SubstitutionConfig : public DefaultRewriterConfig {
public:
    using SubMap = Map<PTRef, PtAsgn, PTRefHash>;

    SubstitutionConfig(Logic &, SubMap const & subMap): subMap(subMap) {}

    PTRef rewrite(PTRef term) override {
        PTRef result = term;
        if (subMap.has(term) && subMap[term].sgn == l_True) {
            result = subMap[term].tr;
        }
        return result;
    }
private:
    SubMap const & subMap;

};

class Substitutor : public Rewriter<SubstitutionConfig> {
    SubstitutionConfig config;

public:
    Substitutor(Logic &logic, Map<PTRef, PtAsgn, PTRefHash> const &substs) :
            Rewriter<SubstitutionConfig>(logic, config),
            config(logic, substs) {}
};