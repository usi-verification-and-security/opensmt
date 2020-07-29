//
// Created by Martin Blicha on 14.06.20.
//

#ifndef OPENSMT_MODELBUILDER_H
#define OPENSMT_MODELBUILDER_H

#include "PTRef.h"
#include "Model.h"

#include <unordered_map>
#include <memory>

class Logic;

class ModelBuilder {

    std::unordered_map<PTRef, PTRef, PTRefHash> assignment;

    Logic& logic;

public:

    ModelBuilder(Logic & logic) : logic(logic) {}

    void addVarValue(PTRef var, PTRef value) {
        auto res = assignment.insert(std::make_pair(var, value));
        assert(res.second); (void)res;
    }

    template<typename TIt>
    void addVarValues(TIt begin, TIt end) {
        assignment.insert(begin, end);
    }

    std::unique_ptr<Model> build() const {
        return std::unique_ptr<Model>(new Model(logic, std::move(assignment)));
    }

    /*
     * Incorporates the given substitution map into the model.
     * PRECONDITIONS: all keys are variables
     */
    void processSubstitutions(Map<PTRef,PtAsgn,PTRefHash> const & subst);
};


#endif //OPENSMT_MODELBUILDER_H
