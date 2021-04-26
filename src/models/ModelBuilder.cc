//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"
#include <unordered_set>

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
        Logic::TFun templateFun(logic.getSymName(sr), formalArgs, logic.getSortRef(val), logic.getDefaultValuePTRef(val));
        definitions.insert(std::move(std::make_pair(sr, std::move(std::make_pair(ValuationNode(), templateFun)))));
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

PTRef ModelBuilder::valuationTreeToFunctionBody(const ValuationNode *root) {
    using QPair = opensmt::pair<const ValuationNode*,std::size_t>;
    std::unordered_map<const ValuationNode*,PTRef,ValuationNodeHash> nodeToFormula;
    vec<QPair> queue;
    queue.push(QPair{root, 0});
    while (queue.size() != 0) {
        auto & el = queue.last();
        auto * node = el.first;
        std::size_t & processedUntil = el.second;
        if (processedUntil < node->children.size()) {
            const ValuationNode *child = (node->children[processedUntil]);
            if (nodeToFormula.find(child) == nodeToFormula.end()) {
                queue.push({QPair{child, 0}});
                nodeToFormula.insert({child,PTRef_Undef});
            }
            processedUntil += 1;
            continue;
        }
        // All children of the node are processed
        if (node->children.empty()) {
            // Base case: the node is a leaf value node.
            PTRef &tr = nodeToFormula.at(node);
            tr = node->value;
        } else {
            PTRef nodeFormula = logic.getDefaultValuePTRef(node->var);
            for (int i = node->children.size()-1; i >= 0; i--) {
                nodeFormula = logic.mkIte(logic.mkEq(node->var, node->children[i]->value), nodeToFormula.at(node->children[i]), nodeFormula);
            }
            nodeToFormula[node] = nodeFormula;
        }
    }
    return nodeToFormula[root];
}