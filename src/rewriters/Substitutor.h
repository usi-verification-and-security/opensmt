//
// Created by Martin Blicha on 10.02.21.
//

#ifndef OPENSMT_SUBSTITUTOR_H
#define OPENSMT_SUBSTITUTOR_H

#endif //OPENSMT_SUBSTITUTOR_H

#include "Rewriter.h"

template <typename TAsgn>
class SubstitutionConfig : public DefaultRewriterConfig<TAsgn> {
private:
    using SubMap = MapWithKeys<PTRef, TAsgn, PTRefHash>;
    SubMap const & subMap;

public:

    SubstitutionConfig<TAsgn>(Logic &, SubMap const & subMap): subMap(subMap) {}
    PTRef rewrite(PTRef term) override {
        PTRef result = term;
        if (subMap.has(term) && DefaultRewriterConfig<TAsgn>::isEnabled(subMap[term])) {
            result = DefaultRewriterConfig<TAsgn>::getAsgnTerm(subMap[term]);
        }
        return result;
    }
};

template<typename TAsgn>
class Substitutor : public Rewriter<SubstitutionConfig<TAsgn>,TAsgn> {
    SubstitutionConfig<TAsgn> config;

public:
    Substitutor(Logic &logic, MapWithKeys<PTRef, TAsgn, PTRefHash> const &substs) :
            Rewriter<SubstitutionConfig<TAsgn>,TAsgn>(logic, config),
            config(logic, substs) {}
};