//
// Created by prova on 28.03.22.
//

#include "TermPrinter.h"
#include <iostream>

bool ReferenceCounterConfig::previsit(PTRef tr) {
    if (not previsitCount.has(tr)) {
        // The first visit
        previsitCount.insert(tr, 1);
    } else {
        // Visit because of the nth child
        auto n = previsitCount[tr] - 1;
        PTRef child = logic.getPterm(tr)[n];
        if (referenceCounts.find(child) == referenceCounts.end()) {
            referenceCounts.insert({child, 1});
        } else {
            ++referenceCounts[child];
        }
        ++previsitCount[tr];
    }
    return true;
}

void TermPrinterConfig::visit(PTRef tr) {
    assert(termStrings.find(tr) == termStrings.end());
    Pterm const & term = logic.getPterm(tr);

    std::string termString = logic.printSym(term.symb());

    if (term.size() == 0) {
        termStrings.emplace(tr, std::move(termString));
        return;
    }
    assert(term.size() > 0);
    termString = '(' + termString + ' ';
    for (int i = 0; i < term.size(); i++) {
        PTRef child = term[i];
        assert(termStrings.find(child) != termStrings.end());
        termString += termStrings.at(child) + (i < term.size()-1 ? " " : "");
        -- refCounts[child];
        if (refCounts[child] == 0) {
            termStrings.erase(child);
        }
    }
    termString += ')';
    termStrings.emplace(tr, std::move(termString));
}

void DagPrinterConfig::visit(PTRef tr) {
    auto getLetSymbol = [&](PTRef tr) { return logic.getLetPrefix() + std::to_string(tr.x); };

    assert(termStrings.find(tr) == termStrings.end());
    Pterm const & term = logic.getPterm(tr);

    std::string symString = logic.printSym(term.symb());

    if (term.size() == 0) {
        assert(definitions.find(tr) == definitions.end());
        termStrings.emplace(tr, std::move(symString));
        return;
    }

    assert(term.size() > 0);
    auto defsInNode = definitions.find(tr);
    std::string openLetStatements;
    std::string closeLetStatements;
    if (defsInNode != definitions.end()) {
        auto const & defTerms = defsInNode->second;
        for (int i = defTerms.size()-1; i >= 0; i--) {
            // Note: Reverse order guarantees that dependencies are respected in let terms
            // Todo: Use parallel lets if there is no dependency between two definitions
            PTRef def = defTerms[i];
            std::string letSymbol = getLetSymbol(def);
            openLetStatements += "(let ((" + letSymbol + " " + termStrings.at(def) + ")) ";
            closeLetStatements += ')';
            termStrings.erase(def);
        }
    }
    std::string termString = symString + ' ';
    for (int i = 0; i < term.size(); i++) {
        PTRef child = term[i];
        bool letDefined = isLetDefined(child);
        assert((termStrings.find(child) != termStrings.end()) or letDefined);
        termString += (letDefined  ? getLetSymbol(child) : termStrings.at(child)) + (i < term.size()-1 ? " " : "");
        if (not letDefined) {
            -- refCounts[child];
            if (refCounts[child] == 0) {
                termStrings.erase(child);
            }
        }
    }
    termString = openLetStatements + '(' + termString + ')' + closeLetStatements;
    termStrings.emplace(tr, std::move(termString));
}

bool SubGraphVisitorConfig::isAnAncestor(PTRef t, PTRef ancestor){
    auto rootNode = nodeFactory.findNode(t);
    assert(rootNode != nullptr);
    auto processed = logic.getTermMarks(logic.getPterm(root).getId());

    std::vector<DFSElement> stack{DFSElement{rootNode, 0}};
    while (not stack.empty()) {
        auto & el = stack.back();
        auto & parents = el.node->parents;
        if (el.processedEdges < parents.size()) {
            auto nextParent = el.node->parents[el.processedEdges++];
            if (nextParent->tr == ancestor) {
                return true;
            }
            auto parentId = logic.getPterm(nextParent->tr).getId();
            if (not processed.isMarked(parentId)) {
                stack.emplace_back(nextParent, 0);
            }
            continue;
        }

        auto currentId = logic.getPterm(el.node->tr).getId();

        assert(not processed.isMarked(currentId));
        processed.mark(currentId);
        stack.pop_back();
    }
    return false;
}

std::vector<PTRef> SubGraphVisitorConfig::removeReversePath(PTRef n, PTRef tr) {
    std::vector<PTRef> path{n};
    while (n != tr) {
        auto &node = *nodeFactory.findNode(n);
        assert(not node.parents.empty());
        n = node.parents.back()->tr;
        node.parents.pop_back();
        path.push_back(n);
    }
    return path;
}

PTRef SubGraphVisitorConfig::findFirstMissingEdge(std::vector<PTRef> const & path) const {
    assert(not path.empty());
    PTRef child = path[0];
    if (path.size() == 1) {
        return child;
    }
    for (unsigned i = 1; i < path.size(); i++) {
        bool found = false;
        for (NodeFactory::Node * parent : nodeFactory.findNode(child)->parents) {
            if (parent->tr == path[i]) {
                found = true;
                break;
            }
        }
        if (not found) {
            return path[i-1];
        }
        child = path[i];
    }
    assert(false);
    return PTRef_Undef;
}

std::string DagPrinter::print(PTRef tr) {
    ReferenceCounterConfig counter(logic);
    TermVisitor(logic, counter).visit(tr);
    std::unordered_map<PTRef,vec<PTRef>,PTRefHash> definitions;
    std::unordered_set<PTRef,PTRefHash> letDefinedTerms;
    for (auto [n, count] : counter.getReferences()) {
        if (not logic.isVar(n) and count > 1) {
            letDefinedTerms.insert(n);
            SubGraphVisitorConfig subGraphVisitorConfig(logic, tr);
            TermVisitor(logic, subGraphVisitorConfig).visit(tr);
            std::vector<PTRef> path = subGraphVisitorConfig.removeReversePath(n, tr);
            assert(not path.empty());
            PTRef definitionTerm = subGraphVisitorConfig.isAnAncestor(n, tr) ? tr : subGraphVisitorConfig.findFirstMissingEdge(path);
            if (definitions.find(definitionTerm) == definitions.end()) {
                definitions.insert({definitionTerm, vec<PTRef>{n}});
            } else {
                definitions.at(definitionTerm).push(n);
            }
        }
    }
    DagPrinterConfig printer(logic, counter.getReferences(), definitions, letDefinedTerms);
    TermVisitor(logic, printer).visit(tr);
    return printer.print(tr);
}