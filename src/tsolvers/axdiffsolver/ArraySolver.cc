//
// Created by Martin Blicha on 22.11.21.
//

#include "ArraySolver.h"

#include "TreeOps.h"

static SolverDescr descr_ax_solver("Array Solver", "Solver for Theory of Arrays");

ArraySolver::ArraySolver(Logic & logic, Egraph & egraph, SMTConfig & config) :
    TSolver((SolverId) descr_ax_solver, (const char *) descr_ax_solver, config),
    logic(logic),
    egraph(egraph)
    { }

ArraySolver::~ArraySolver() {

}

void ArraySolver::clearSolver() {
    clear();
    TSolver::clearSolver();
}

bool ArraySolver::assertLit(PtAsgn) {
    // TODO: what should we remember from this?
    assert(false);
    return true;
}

void ArraySolver::pushBacktrackPoint() {
    TSolver::pushBacktrackPoint();
}

void ArraySolver::popBacktrackPoint() {
    clear();
    TSolver::popBacktrackPoint();
}

void ArraySolver::popBacktrackPoints(unsigned int i) {
    clear();
    TSolver::popBacktrackPoints(i);
}

TRes ArraySolver::check(bool complete) {
    if (not valid) {
        assert(nodes.empty() and rootsMap.empty());
        for (ERef arrayTerm : arrayTerms) {
            ERef root = getRoot(arrayTerm);
            if (rootsMap.find(root) == rootsMap.end()) {
                NodeRef nodeRef {static_cast<unsigned int>(nodes.size())};
                nodes.emplace_back(root);
                rootsMap.insert({root, nodeRef});
            }
        }
        for (ERef store : storeTerms) {
            merge(store);
        }
        valid = true;
    }
    if (not checkReadOverWeakEq()) {
        return TRes::UNSAT;
    }
    return TRes::SAT;
}

void ArraySolver::fillTheoryFunctions(ModelBuilder & builder) const {
    TSolver::fillTheoryFunctions(builder);
}

void ArraySolver::computeModel() {

}

void ArraySolver::getConflict(vec<PtAsgn> & vec) {

}

PtAsgn_reason ArraySolver::getDeduction() {
    return TSolver::getDeduction();
}

void ArraySolver::declareAtom(PTRef tr) {
    class TermCollectorConfig : public DefaultVisitorConfig {
        Logic & logic;
        ArraySolver::Terms & arrayTerms;
        ArraySolver::Terms & storeTerms;
        ArraySolver::Terms & selectTerms;
        Egraph & egraph;

    public:
        TermCollectorConfig(Logic & logic, Terms & arrayTerms, Terms & storeTerms, Terms & selectTerms, Egraph & egraph)
        : logic(logic), arrayTerms(arrayTerms), storeTerms(storeTerms), selectTerms(selectTerms), egraph(egraph) {}

        void visit(PTRef term) override {
            if (logic.isArraySort(logic.getSortRef(term))) {
                ERef eref = egraph.termToERef(term);
                arrayTerms.insert(eref);
                if (logic.isArrayStore(logic.getSymRef(term))) {
                    storeTerms.insert(eref);
                }
            } else if (logic.isArraySelect(logic.getSymRef(term))) {
                ERef eref = egraph.termToERef(term);
                selectTerms.insert(eref);
            }
        }
    };

    TermCollectorConfig config(logic, arrayTerms, storeTerms, selectTerms, egraph);
    TermVisitor<TermCollectorConfig>(logic, config).visit(tr);
}

Logic & ArraySolver::getLogic() {
    return logic;
}

bool ArraySolver::isValid(PTRef tr) {
    return egraph.isValid(tr);
}


/*
 * Internal methods for manipulating weak equivalence graph
 */

void ArraySolver::makeIndexedWeakRepresentative(NodeRef nodeRef) {
    ArrayNode & node = getNode(nodeRef);
    NodeRef secondaryRef = node.secondaryEdge;
    if (secondaryRef != NodeRef_Undef) {
        if (getNode(secondaryRef).primaryIndex != node.primaryIndex) {
            node.secondaryEdge = getNode(secondaryRef).primaryEdge;
            makeIndexedWeakRepresentative(nodeRef);
        } else {
            makeIndexedWeakRepresentative(secondaryRef);
            // invert secondary edge
            getNode(secondaryRef).secondaryEdge = nodeRef;
            node.secondaryEdge = NodeRef_Undef;
        }
    }
}

void ArraySolver::makeWeakRepresentative(NodeRef nodeRef) {
    ArrayNode & node = getNode(nodeRef);
    NodeRef parentRef = node.primaryEdge;
    if (parentRef != NodeRef_Undef) {
        makeWeakRepresentative(parentRef);
        // Invert primary edge
        getNode(parentRef).primaryEdge = nodeRef;
        node.primaryEdge = NodeRef_Undef;
        // Make representative for i-weak equivalence class
        makeIndexedWeakRepresentative(nodeRef);
    }
}

void ArraySolver::merge(ERef storeTerm) {
    assert(logic.isArrayStore(logic.getSymRef(egraph.ERefToTerm(storeTerm))));
    ERef arrayTerm = getArrayFromStore(storeTerm);
    ERef indexTerm = getRoot(getIndexFromStore(storeTerm));
    NodeRef arrayNode = getNodeRef(getRoot(arrayTerm));
    NodeRef storeNode = getNodeRef(getRoot(storeTerm));
    if (arrayNode == storeNode) { return; }
    makeWeakRepresentative(arrayNode);
    if (getRepresentative(storeNode) == arrayNode) {
        Map<ERef, bool, ERefHash> forbiddenIndices;
        forbiddenIndices.insert(indexTerm, true);
        mergeSecondary(storeNode, arrayNode, forbiddenIndices);
    } else {
        // new primary edge
        getNode(arrayNode).primaryEdge = storeNode;
        getNode(arrayNode).primaryIndex = indexTerm;
    }
}

void ArraySolver::mergeSecondary(NodeRef nodeRef, NodeRef root, Map<ERef, bool, ERefHash> & forbiddenIndices) {
    if (nodeRef == root) { return; }
    ArrayNode & node = getNode(nodeRef);
    ERef primaryIndex = node.primaryIndex;
    if (not forbiddenIndices.has(primaryIndex) and getIndexedRepresentative(nodeRef, primaryIndex) != root) {
        makeIndexedWeakRepresentative(nodeRef);
        node.secondaryEdge = root;
    }
    forbiddenIndices.insert(primaryIndex, true);
    mergeSecondary(node.primaryEdge, root, forbiddenIndices);
}

bool ArraySolver::checkReadOverWeakEq() {
    std::unordered_map<ERef, vec<ERef>, ERefHash> indicesToSelects;
    for (ERef select : selectTerms) {
        ERef index = getIndexFromSelect(select);
        ERef root = egraph.getRoot(index);
        indicesToSelects[root].push(select);
    }
    for (auto const & entry : indicesToSelects) {
        auto const & selects = entry.second;
        if (selects.size() < 2) { continue; }
        // iterate over all pairs for now
        for (int i = 0; i < selects.size(); ++i) {
            ERef first = selects[i];
            for (int j = 0; j < i; ++j) {
                ERef second = selects[j];
                if (egraph.getRoot(second) != egraph.getRoot(first)) {
                    NodeRef arrayFirst = getNodeRef(getRoot(getArrayFromSelect(first)));
                    NodeRef arraySecond = getNodeRef(getRoot(getArrayFromSelect(second)));
                    if (arrayFirst == arraySecond or getIndexedRepresentative(arrayFirst, entry.first) == getIndexedRepresentative(arraySecond, entry.first)) {
                        bool mergable = egraph.canBeMerged(first, second);
                        // if the selects are unmergable, we have a conflict and have to remember the reason
                        if (not mergable) {
                            // TODO: remember the conflict clause
//                            throw std::logic_error("Not implemented yet!");
                            return false;
                        }
                    }
                }
            }
        }
    }
    return true;
}

void ArraySolver::clear() {
    nodes.clear();
    rootsMap.clear();
    valid = false;
}

