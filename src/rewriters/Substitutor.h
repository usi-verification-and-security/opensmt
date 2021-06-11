//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_SUBSTITUTOR_H
#define OPENSMT_SUBSTITUTOR_H

#endif //OPENSMT_SUBSTITUTOR_H

#include "Rewriter.h"

class SubstitutionConfig : public DefaultRewriterConfig {
public:
    using SubMap = MapWithKeys<PTRef, PtAsgn, PTRefHash>;

    SubstitutionConfig(Logic & logic, SubMap const & subMap): logic(logic), subMap(subMap) {}

    PTRef rewrite(PTRef term) override {
        PTRef result = term;
        if (logic.isVar(term) || logic.isConstant(term)) {
            if (subMap.has(term) && subMap[term].sgn == l_True)
                result = subMap[term].tr;
            else
                result = term;
            assert(not logic.isConstant(term) || result == term);
            assert(result != PTRef_Undef);
        } else {
            // The "inductive" case
            if (subMap.has(term) && subMap[term].sgn == l_True) {
                result = subMap[term].tr;
            } else { // Nothing to do here
            }
        }
        return result;
    }
private:
    Logic & logic;
    SubMap const & subMap;

};

class Substitutor : public Rewriter<SubstitutionConfig> {
    SubstitutionConfig config;

public:
    Substitutor(Logic &logic, SubstitutionConfig::SubMap const &substs) :
            Rewriter<SubstitutionConfig>(logic, config),
            config(logic, substs) {}
};