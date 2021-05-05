//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"
#include <unordered_set>

int ModelBuilder::ValuationNode::counter = 0;

std::unique_ptr<Model> ModelBuilder::build() {
    std::unordered_map<SymRef,TemplateFunction,SymRefHash> builtDefinitions;
    for (auto & symbolSigVal : definitions) {
        const ValuationNode * valuationNode = symbolSigVal.second.second;
        SRef sr = logic.getSortRef(symbolSigVal.first);
        PTRef body = valuationTreeToFunctionBody(valuationNode, sr);
        // todo: how to free the valuationNode?
        TemplateFunction templateFun(std::move(symbolSigVal.second.first), body);
        builtDefinitions[symbolSigVal.first] = std::move(templateFun);
    }
    return std::unique_ptr<Model>(new Model(logic, assignment, builtDefinitions));
}

void ModelBuilder::addToTheoryFunction(SymRef sr, vec<PTRef> vals, PTRef val)
{
    if (logic.getSortRef(sr) != logic.getSortRef(val)) {
        throw OsmtApiException("Incompatible sort for symbol valuation");
    }
    Symbol & sym = logic.getSym(sr);
    if (sym.nargs() != vals.size_()) {
        throw OsmtApiException("Incorrect valuation for symbol: argument and valuation size do not match");
    }
    for (int i = 0; i < vals.size(); i++) {
        if (sym[i] != logic.getSortRef(vals[i])) {
            throw OsmtApiException("Incorrect valuation for symbol: sort mismatch");
        }
    }

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
        FunctionSignature templateSig(logic.getSymName(sr), std::move(formalArgs), logic.getSortRef(sr));
        definitions.insert({sr,opensmt::pair<FunctionSignature,ValuationNode*>{std::move(templateSig), nullptr}});
    }
    auto & signatureAndValuation = definitions.at(sr);
    FunctionSignature & templateSignature = signatureAndValuation.first;
    const vec<PTRef> & formalArgs = templateSignature.getArgs();
    vec<opensmt::pair<PTRef,PTRef>> valuation; valuation.capacity(vals.size());
    for (int i = 0; i < vals.size(); i++) {
        valuation.push({formalArgs[i], vals[i]});
    }
    assert(logic.getSortRef(val) == logic.getSortRef(sr));
    signatureAndValuation.second = addToValuationTree(valuation, val, signatureAndValuation.second);
}
    }
    return root;
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