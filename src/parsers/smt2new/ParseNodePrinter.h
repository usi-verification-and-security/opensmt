//
// Created by Antti Hyvärinen on 26.10.22.
//

#ifndef OPENSMT_PARSENODEPRINTER_H
#define OPENSMT_PARSENODEPRINTER_H

#include "smt2newcontext.h"
#include <numeric>

namespace opensmt {

class nodeToString {
public:
    std::string operator()(SymbolNode const & node) {
        if (auto str = std::get_if<std::unique_ptr<std::string>>(&node.name)) {
            return {**str};
        } else if (auto specConstNode = std::get_if<std::unique_ptr<SpecConstNode>>(&node.name)) {
            return {*(**specConstNode).value};
        }
        assert(false);
        return {};
    }
    std::string operator()(SortNode const & node) {
        // Todo: better printing
        return operator()(*node.identifier->symbol);
    }
    std::string operator()(IdentifierNode const & identifier) {
        return operator()(*identifier.symbol);
    }
    std::string operator()(SExpr const * root) {
        struct QEl { SExpr const * sexpr; unsigned long count; };
        std::vector<std::string> childStrings;
        std::vector<QEl> stack;
        stack.push_back({root, 0});
        while (not stack.empty()) {
            auto & [sexpr, count] = stack.back();
            if (auto vec_p = std::get_if<std::unique_ptr<std::vector<SExpr*>>>(&(*sexpr).data)) {
                assert(*vec_p);
                auto & vec = **vec_p;
                if (count < vec.size()) {
                    // Note: the order is important since `count` is a reference to `stack`
                    ++count;
                    stack.push_back({ vec[count-1], 0 });
                    continue;
                }
                // Vector, all children processed
                auto childStringStart = childStrings.end() - vec.size();
                auto siblingString = std::accumulate(childStringStart, childStrings.end(), std::string(),
                                [](std::string & a, const std::string & b) {
                                    return a += (a.empty() ? "" : " ") + b;
                                });
                childStrings.erase(childStringStart, childStrings.end());
                childStrings.emplace_back("(" + siblingString + ")");
            } else if (auto constNode = std::get_if<std::unique_ptr<SpecConstNode>>(&(*sexpr).data)) {
                assert(*constNode);
                childStrings.push_back(*(**constNode).value);
            } else if (auto symbolNode = std::get_if<std::unique_ptr<SymbolNode>>(&(*sexpr).data)) {
                assert(*symbolNode);
                childStrings.push_back(operator()(**symbolNode));
            } else if (auto string = std::get_if<std::unique_ptr<std::string>>(&(*sexpr).data)) {
                assert(*string);
                childStrings.push_back(**string);
            }
            stack.pop_back();
        }
        if (auto sexprVec_p = std::get_if<std::unique_ptr<std::vector<SExpr*>>>(&root->data)) {
            auto sexprsString = std::accumulate((*sexprVec_p)->begin(), (*sexprVec_p)->end(), std::string{},
                                [this](std::string & a, SExpr const * b) {
                                    return a += (a.empty() ? "" : " ") + operator()(b);
                                });
            return "(" + sexprsString + ")";
        } else {
            assert(childStrings.size() == 1);
            return childStrings[0];
        }
    }
    std::string operator() (AttributeValueNode const & attributeValue) {
        if (auto specConst_p = std::get_if<std::unique_ptr<SpecConstNode>>(&attributeValue.value)) {
            return {*(**specConst_p).value};
        } else if (auto symbol_p = std::get_if<std::unique_ptr<SymbolNode>>(&attributeValue.value)) {
            return operator()(**symbol_p);
        } else if (auto sexprVec_p = std::get_if<std::unique_ptr<std::vector<SExpr*>>>(&attributeValue.value)) {
            auto sexprsString = std::accumulate((*sexprVec_p)->begin(), (*sexprVec_p)->end(), std::string("("),
                                            [this](std::string & a, SExpr const * b) {
                                                return a += operator()(b) + ' ';
                                            });
            return sexprsString += ')';
        } else {
            assert(false);
            return {};
        }
    }
};





}
#endif // OPENSMT_PARSENODEPRINTER_H
