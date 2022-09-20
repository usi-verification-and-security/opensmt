/*
* Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
*
* SPDX-License-Identifier: MIT
*/

#include "smt2newcontext.h"
namespace {
    struct Qel {
       TermNode* node;
       uint32_t processed;
    };
    bool checkProcessedProperty(Qel & element) {
        auto & [termNode, processed] = element;
        assert(termNode);
        if (auto normalTermNode = dynamic_cast<NormalTermNode*>(termNode)) {
            return processed == normalTermNode->arguments->size();
        } else if (auto letTermNode = dynamic_cast<LetTermNode*>(termNode)) {
            return processed == letTermNode->arguments->size() + letTermNode->bindings->size();
        }
        assert(false);
        return false;
    }
}

TermNode::~TermNode() {
    std::vector<Qel> queue;
    queue.emplace_back(Qel{this, static_cast<uint32_t>(0)});
    while (not queue.empty()) {
        auto & [termNode, processed] = queue.back();
        auto & children = *(termNode->arguments);
        if (processed < children.size()) {
            ++ processed;
            queue.emplace_back(Qel{children[processed - 1], 0});
        } else if (auto letTermNode = dynamic_cast<LetTermNode*>(termNode)) {
            auto & bindings = *(letTermNode->bindings);
            assert(children.size() == 1);
            if (processed < bindings.size()+1) {
                ++ processed;
                queue.emplace_back(Qel{bindings[processed -1]->term, 0});
            }
        }
        assert(termNode);
        assert(checkProcessedProperty(queue.back()));

        for (auto child : *arguments) {
            assert(child->arguments->empty());
            delete child;
        }
        termNode->arguments->clear(); // delete is not called on the pointers
        queue.pop_back();
    }
}
