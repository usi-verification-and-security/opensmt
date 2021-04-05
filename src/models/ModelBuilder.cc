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
            assignCopy.insert(std::make_pair(entry->key, val));
        }
    }
    this->assignment = std::move(assignCopy);
}

std::unique_ptr<Model> ModelBuilder::build() const {
    return std::unique_ptr<Model>(new Model(logic, std::move(assignment), std::move(definitions)));
}

std::string ModelBuilder::getFormalArgBaseNameForSymbol(SymRef sr) const {
    const std::string & symName(logic.getSymName(sr));

    // Collision is possible if formalArgDefaultPrefix can be extended to symName by adding at least one character.
    bool collisionPossible = formalArgDefaultPrefix == symName.substr(0, formalArgDefaultPrefix.size());

    if (collisionPossible) {
        // Modify the base by changing the first character to a different character.  Collision is then not possible
        std::string newPrefix(formalArgDefaultPrefix);
        newPrefix[0] = (symName[0] + 1) % 26 + 'a';
        assert(newPrefix[0] != symName[0]);
        return newPrefix;
    }
    return formalArgDefaultPrefix;
}

void ModelBuilder::addToTheoryFunction(SymRef sr, vec<PTRef> vals, PTRef val)
{
    if (not hasTheoryFunction(sr)) {
        vec<PTRef> formalArgs; formalArgs.capacity(vals.size());
        std::stringstream ss;
        std::string symName(logic.getSymName(sr));
        // Ensure that no formal arg name collides with the function name
        std::string formalArgPrefix(getFormalArgBaseNameForSymbol(sr));

        for (PTRef v : vals) {
            ss << formalArgPrefix << uniqueNum++;
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