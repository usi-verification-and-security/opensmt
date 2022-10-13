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
    bool checkProcessedProperty(TermNode * termNode, size_t processed) {
        assert(termNode);
        if (auto letTermNode = dynamic_cast<LetTermNode*>(termNode)) {
            return processed == letTermNode->arguments->size() + letTermNode->bindings->size();
        }
        return processed == termNode->arguments->size();
    }
}

TermNode::~TermNode() {
    std::vector<Qel> queue;
    queue.emplace_back(Qel{this, static_cast<uint32_t>(0)});
    while (not queue.empty()) {
        auto & [termNode, processed] = queue.back();
        if (not termNode->arguments) {
            queue.pop_back();
            continue;
        }
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
        assert(checkProcessedProperty(termNode, processed));

        for (auto child : *arguments) {
            assert(child->arguments->empty());
            delete child;
        }
        termNode->arguments->clear(); // delete is not called on the pointers
        queue.pop_back();
    }
}
