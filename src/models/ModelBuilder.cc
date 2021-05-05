//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"

void ModelBuilder::processSubstitutions(Map<PTRef,PtAsgn,PTRefHash> const & subst) {
    Map<PTRef,PtAsgn,PTRefHash> copy;
    subst.copyTo(copy);
    logic.substitutionsTransitiveClosure(copy);
    auto assignCopy = this->assignment;
    auto model = this->build();
    auto entries = copy.getKeysAndValsPtrs();
    for (auto const * const entry : entries) {
        if (logic.isIte(entry->key)) {
            // We store only values of reals variables
            continue;
        }
        assert(logic.isVar(entry->key));
        if (entry->data.sgn == l_True) {
            PTRef mappedTerm = entry->data.tr;
            PTRef val = model->evaluate(mappedTerm);
//            assert(logic.isConstant(val));
            assignCopy.insert(std::make_pair(entry->key, val));
        }
    }
    this->assignment = std::move(assignCopy);
}

std::unique_ptr<Model> ModelBuilder::build() const {
    return std::unique_ptr<Model>(new Model(logic, std::move(assignment), std::move(definitions)));
}

void ModelBuilder::addToTheoryFunction(SymRef sr, vec<PTRef> vals, PTRef val)
{
    if (not hasTheoryFunction(sr)) {
        vec<PTRef> formalArgs; formalArgs.capacity(vals.size());
        std::stringstream ss;
        for (PTRef v : vals) {
            ss << "x" << uniqueNum++;
            formalArgs.push(logic.mkVar(logic.getSortRef(v), ss.str().c_str()));
        }
        Logic::TFun templateFun(logic.getSymName(sr), formalArgs, logic.getSortRef(val), logic.getDefaultValuePTRef(val));
        definitions.insert(std::make_pair(sr, templateFun));
    }
    Logic::TFun & templateFun = definitions.at(sr);
    const vec<PTRef> & formalArgs = templateFun.getArgs();
    vec<PTRef> and_args; and_args.capacity(vals.size());
    for (int i = 0; i < vals.size(); i++) {
        and_args.push(logic.mkEq(formalArgs[i], vals[i]));
    }
    PTRef cond = logic.mkAnd(and_args);
    PTRef old_body = templateFun.getBody();
    templateFun.updateBody(logic.mkIte(cond, val, old_body));
}