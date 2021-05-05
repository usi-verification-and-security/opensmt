//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"


std::unique_ptr<Model> ModelBuilder::build() const {
    return std::unique_ptr<Model>(new Model(logic, assignment, definitions));
}

void ModelBuilder::addToTheoryFunction(SymRef sr, vec<PTRef> vals, PTRef val)
{
    if (not hasTheoryFunction(sr)) {
        vec<PTRef> formalArgs; formalArgs.capacity(vals.size());
        std::string symName(logic.getSymName(sr));
        // Ensure that no formal arg name collides with the function name
        std::string formalArgPrefix(Model::getFormalArgBaseNameForSymbol(logic, sr, formalArgDefaultPrefix));

        for (PTRef v : vals) {
            std::stringstream ss;
            ss << formalArgPrefix << uniqueNum++;
            formalArgs.push(logic.mkVar(logic.getSortRef(v), ss.str().c_str()));
        }
        TemplateFunction templateFun(logic.getSymName(sr), formalArgs, logic.getSortRef(val), logic.getDefaultValuePTRef(val));
        definitions.insert(std::make_pair(sr, templateFun));
    }
    TemplateFunction & templateFun = definitions.at(sr);
    const vec<PTRef> & formalArgs = templateFun.getArgs();
    vec<PTRef> and_args; and_args.capacity(vals.size());
    for (int i = 0; i < vals.size(); i++) {
        and_args.push(logic.mkEq(formalArgs[i], vals[i]));
    }
    PTRef cond = logic.mkAnd(and_args);
    PTRef old_body = templateFun.getBody();
    templateFun.updateBody(logic.mkIte(cond, val, old_body));
}