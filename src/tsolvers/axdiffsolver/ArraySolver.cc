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

bool ArraySolver::assertLit(PtAsgn literal) {
    if (logic.isEquality(literal.tr)) {
        if (literal.sgn == l_True) {
            clear();
        } else if (literal.sgn == l_False) {
            for (auto & lemma : lemmas) {
                auto & undecided = lemma.undecidedEqualities;
                auto it = undecided.find(literal.tr);
                if (it != undecided.end()) {
                    undecided.erase(it);
                }
                if (undecided.empty()) {
                    has_explanation = true;
                    computeExplanation(lemma.equality);
                    return false;
                }
            }
        }
    }
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
        buildWeakEq();
    }
    for (auto const & lemma : this->lemmas) {
        if (lemma.undecidedEqualities.empty()) {
            has_explanation = true;
            computeExplanation(lemma.equality);
            return TRes::UNSAT;
        }
    }
    if (complete) {
        // TODO: if full check, and we have some undecided literal in lemmas, we need to create a split clause to inform SAT solver that we need more information
    }
    return TRes::SAT;
}

void ArraySolver::fillTheoryFunctions(ModelBuilder & builder) const {
    TSolver::fillTheoryFunctions(builder);
}

void ArraySolver::computeModel() {

}

void ArraySolver::getConflict(vec<PtAsgn> & vec) {
    assert(vec.size() == 0);
    assert(has_explanation);
    assert(explanation.size() > 0);
    for (auto lit : explanation) {
        vec.push(lit);
    }
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

    if(logic.isEquality(tr)) {
        setKnown(tr);
    }
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
        if (getIndexOfPrimaryEdge(getNode(secondaryRef)) != getIndexOfPrimaryEdge(node)) {
            node.secondaryEdge = getNode(secondaryRef).primaryEdge; // TODO: Does this affects secondary store?
            makeIndexedWeakRepresentative(nodeRef);
        } else {
            makeIndexedWeakRepresentative(secondaryRef);
            // invert secondary edge
            getNode(secondaryRef).secondaryEdge = nodeRef;
            getNode(secondaryRef).secondaryStore = node.secondaryStore;
            node.secondaryEdge = NodeRef_Undef;
            node.secondaryStore = ERef_Undef;
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
        getNode(parentRef).primaryStore = node.primaryStore;
        node.primaryEdge = NodeRef_Undef;
        node.primaryStore = ERef_Undef;
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
        mergeSecondary(storeNode, arrayNode, storeTerm, forbiddenIndices);
    } else {
        // new primary edge
        getNode(arrayNode).primaryEdge = storeNode;
        getNode(arrayNode).primaryStore = storeTerm;
    }
}

void ArraySolver::mergeSecondary(NodeRef nodeRef, NodeRef root, ERef store, Map<ERef, bool, ERefHash> & forbiddenIndices) {
    if (nodeRef == root) { return; }
    ArrayNode & node = getNode(nodeRef);
    ERef primaryIndex = getIndexOfPrimaryEdge(node);
    assert(getRoot(primaryIndex) == primaryIndex);
    if (not forbiddenIndices.has(primaryIndex) and getIndexedRepresentative(nodeRef, primaryIndex) != root) {
        makeIndexedWeakRepresentative(nodeRef);
        node.secondaryEdge = root;
        node.secondaryStore = store;
    }
    forbiddenIndices.insert(primaryIndex, true);
    mergeSecondary(node.primaryEdge, root, store, forbiddenIndices);
}

void ArraySolver::buildWeakEq() {
    assert(not valid);
    assert(nodes.empty() and rootsMap.empty() and lemmas.empty());
    for (ERef arrayTerm : arrayTerms) {
        ERef root = getRoot(arrayTerm);
        if (rootsMap.find(root) == rootsMap.end()) {
            NodeRef nodeRef {static_cast<unsigned int>(nodes.size())};
            nodes.emplace_back();
            rootsMap.insert({root, nodeRef});
        }
    }
    for (ERef store : storeTerms) {
        merge(store);
    }
    collectLemmaConditions();
    valid = true;
}

void ArraySolver::collectLemmaConditions() {
    std::unordered_map<ERef, vec<ERef>, ERefHash> indicesToSelects;
    for (ERef select : selectTerms) {
        ERef index = getIndexFromSelect(select);
        ERef root = egraph.getRoot(index);
        indicesToSelects[root].push(select);
    }
    for (auto const & entry : indicesToSelects) {
        ERef index = entry.first;
        auto const & selects = entry.second;
        if (selects.size() < 2) { continue; }
        // TODO: Figure out better way how to compute all candidates for lemmas
        for (auto firstIt = selects.begin(); firstIt != selects.end(); ++firstIt) {
            ERef first = *firstIt;
            ERef firstRoot = getRoot(first);
            for (auto secondIt = selects.begin(); secondIt != firstIt; ++secondIt) {
                ERef second = *secondIt;
                if (firstRoot == getRoot(second)) { continue; } // The selects are already the same, no lemma needed
                NodeRef arrayFirst = getNodeRef(getRoot(getArrayFromSelect(first)));
                NodeRef arraySecond = getNodeRef(getRoot(getArrayFromSelect(second)));
                if (arrayFirst == arraySecond or getIndexedRepresentative(arrayFirst, index) == getIndexedRepresentative(arraySecond, index)) {
                    LemmaConditions lemmaConditions;
                    PTRef equalityOfSelects = getEquality(first, second);
                    lemmaConditions.equality = equalityOfSelects;
                    if (not isFalsified(equalityOfSelects)) {
                        assert(not isSatisfied(equalityOfSelects));
                        lemmaConditions.undecidedEqualities.insert(equalityOfSelects);
                    }
                    auto storeIndices = Traversal(*this).computeStoreIndices(arrayFirst, arraySecond, index);
                    for (ERef storeIndex : storeIndices) {
                        assert(storeIndex != index);
                        PTRef equalityOfIndices = getEquality(index, storeIndex);
                        if (not isFalsified(equalityOfIndices)) {
                            assert(not isSatisfied(equalityOfIndices));
                            lemmaConditions.undecidedEqualities.insert(equalityOfIndices);
                        }
                    }
                    this->lemmas.push_back(std::move(lemmaConditions));
                }
            }
        }
    }
}

PTRef ArraySolver::getEquality(ERef lhs, ERef rhs) {
    return logic.mkEq(egraph.ERefToTerm(lhs), egraph.ERefToTerm(rhs));
}

bool ArraySolver::isFalsified(PTRef equality) {
    return egraph.hasPolarity(equality) and egraph.getPolarity(equality) == l_False;
}

bool ArraySolver::isSatisfied(PTRef equality) {
    return egraph.hasPolarity(equality) and egraph.getPolarity(equality) == l_True;
}

/*
 * Collect the store indices on the path from array1 to array2 using only indices different from index.
 */
std::unordered_set<ERef, ERefHash> ArraySolver::Traversal::computeStoreIndices(NodeRef array1, NodeRef array2, ERef index) {
    assert(index == getRoot(index));
    Cursor cursor1(getSolver(), array1);
    Cursor cursor2(getSolver(), array2);
    std::unordered_set<ERef, ERefHash> indices;
    auto steps1 = cursor1.countSecondaryEdges(index);
    auto steps2 = cursor2.countSecondaryEdges(index);
    while (steps1 > steps2) {
        cursor1.collectOneSecondary(index, indices);
        --steps1;
    }
    while (steps2 > steps1) {
        cursor2.collectOneSecondary(index, indices);
        --steps2;
    }
    while (findSecondaryNode(cursor1.currentNodeRef(), index) != findSecondaryNode(cursor2.currentNodeRef(), index)) {
        cursor1.collectOneSecondary(index, indices);
        cursor2.collectOneSecondary(index, indices);
    }
    cursor1.collectOverPrimaries(cursor2.currentNodeRef(), indices);
    return indices;
}

void ArraySolver::computeExplanation(PTRef equality) {
    assert(logic.isEquality(equality));
    PTRef lhs = logic.getPterm(equality)[0];
    PTRef rhs = logic.getPterm(equality)[1];
    assert(logic.isArraySelect(logic.getSymRef(lhs)));
    assert(logic.isArraySelect(logic.getSymRef(rhs)));
    ERef array1 = egraph.termToERef(logic.getPterm(lhs)[0]);
    ERef array2 = egraph.termToERef(logic.getPterm(rhs)[0]);
    ERef index1 = egraph.termToERef(logic.getPterm(lhs)[1]);
    ERef index2 = egraph.termToERef(logic.getPterm(rhs)[1]);

    // collect literals explaining why array1 is weakly equivalent to array2
    auto conflictExplanation = explainWeakEquivalencePath(array1, array2, getRoot(index1));
    // collect literals explaining why index1 is equivalent to index2 in Egraph
    if (index1 != index2) {
        auto indexExplanation = egraph.explainer->explain(index1, index2);
        for (PtAsgn lit : indexExplanation) {
            conflictExplanation.insert(lit);
        }
    }
    this->has_explanation = true;
    this->explanation.clear();
    for (auto lit : conflictExplanation) {
        this->explanation.push(lit);
    }
}

ArraySolver::ExplanationCollection ArraySolver::explainWeakEquivalencePath(ERef array1, ERef array2, ERef index) {
    assert(getRoot(index) == index);
    NodeRef node1 = getNodeRef(getRoot(array1));
    NodeRef node2 = getNodeRef(getRoot(array2));
    assert(getIndexedRepresentative(node1, index) == getIndexedRepresentative(node2, index));

    Traversal traversal(*this);
    IndicesCollection storeIndices;
    ExplanationCollection explanations;

    auto count1 = traversal.countSecondaryEdges(node1, index);
    auto count2 = traversal.countSecondaryEdges(node2, index);
    ExplanationCursor cursor1(traversal, node1, array1);
    ExplanationCursor cursor2(traversal, node2, array2);
    while (count1 > count2) {
        cursor1.collectOneSecondary(index, storeIndices, explanations);
    }
    while (count2 > count1) {
        cursor2.collectOneSecondary(index, storeIndices, explanations);
    }
    while (traversal.findSecondaryNode(cursor1.getNode(), index) != traversal.findSecondaryNode(cursor2.getNode(), index)) {
        cursor1.collectOneSecondary(index, storeIndices, explanations);
        cursor2.collectOneSecondary(index, storeIndices, explanations);
    }
    cursor1.collectPrimaries(cursor2, storeIndices, explanations);
    for (ERef storeIndex : storeIndices) {
        PTRef eq = getEquality(storeIndex, index);
        assert(isFalsified(eq));
        explanations.insert(PtAsgn(eq, l_False));
    }
    return explanations;
}

void ArraySolver::clear() {
    lemmas.clear();
    nodes.clear();
    rootsMap.clear();
    valid = false;
}

//////////// Cursor traversing the graph of weak equivalence

unsigned int ArraySolver::Traversal::countSecondaryEdges(NodeRef start, ERef index) const {
    assert(getRoot(index) == index);
    unsigned count = 0;
    NodeRef currentRef = start;
    while(getNode(currentRef).primaryEdge != NodeRef_Undef) {
        auto const & currentNode = getNode(currentRef);
        auto primaryIndex = solver.getIndexOfPrimaryEdge(currentNode);
        assert(getRoot(primaryIndex) == primaryIndex);
        if (primaryIndex == index) {
            if (currentNode.secondaryEdge == NodeRef_Undef) {
                break;
            } else {
                currentRef = currentNode.secondaryEdge;
                ++count;
            }
        } else {
            currentRef = currentNode.primaryEdge;
        }
    }
    return count;
}

NodeRef ArraySolver::Traversal::findSecondaryNode(NodeRef nodeRef, ERef index) const {
    assert(getRoot(index) == index);
    while (getNode(nodeRef).primaryEdge != NodeRef_Undef and getIndexOfPrimaryEdge(getNode(nodeRef)) != index) {
        nodeRef = getNode(nodeRef).primaryEdge;
    }
    return nodeRef;
}

void ArraySolver::Cursor::collectOneSecondary(ERef index, IndicesCollection & indices) {
    NodeRef secondaryNode = traversal.findSecondaryNode(this->node, index);
    ERef store = getNode(secondaryNode).secondaryStore;
    auto & solver = traversal.getSolver();
    ERef array = solver.getArrayFromStore(store);
    NodeRef arrayNode = solver.getNodeRef(solver.getRoot(array));
    NodeRef storeNode = solver.getNodeRef(solver.getRoot(store));
    if (traversal.findSecondaryNode(arrayNode, index) == secondaryNode) {
        collectOverPrimaries(arrayNode, indices);
        this->node = storeNode;
    } else if (traversal.findSecondaryNode(storeNode, index) == secondaryNode) {
        collectOverPrimaries(storeNode, indices);
        this->node = arrayNode;
    } else {
        // TODO: change to assert and avoid the second check after verifying this is true
        throw std::logic_error("Unreachable!");
    }
    indices.insert(solver.getIndexFromStore(store));
}

unsigned int ArraySolver::Traversal::countPrimaryEdges(NodeRef start) const {
    unsigned count = 0;
    NodeRef current = start;
    while (getNode(current).primaryEdge != NodeRef_Undef) {
        current = getNode(current).primaryEdge;
        ++count;
    }
    return count;
}

void ArraySolver::Cursor::collectOverPrimaries(NodeRef destination, IndicesCollection & indices) {
    // compute the steps to the common root
    auto steps1 = countPrimaryEdges();
    auto steps2 = Cursor(traversal.getSolver(),destination).countPrimaryEdges();
    // if one needs more step than the other, follow the primary edges until the steps equal
    while (steps1 > steps2) {
        indices.insert(traversal.getIndexOfPrimaryEdge(getNode(this->node)));
        this->node = getNode(this->node).primaryEdge;
        steps1--;
    }
    while (steps2 > steps1) {
        indices.insert(traversal.getIndexOfPrimaryEdge(getNode(destination)));
        destination = getNode(destination).primaryEdge;
        steps2--;
    }
    // now follow the primary edge from both nodes until the common ancestor is found
    while (this->node != destination) {
        indices.insert(traversal.getIndexOfPrimaryEdge(getNode(this->node)));
        indices.insert(traversal.getIndexOfPrimaryEdge(getNode(destination)));
        this->node = getNode(this->node).primaryEdge;
        destination = getNode(destination).primaryEdge;
    }
}

void ArraySolver::ExplanationCursor::collectOneSecondary(
    ERef index,
    IndicesCollection & indices,
    ExplanationCollection & explanations) {

    NodeRef secondaryRef = traversal.findSecondaryNode(this->node, index);
    ERef secondaryStore = traversal.getNode(secondaryRef).secondaryStore;
    assert(secondaryStore != ERef_Undef);
    auto & solver = traversal.getSolver();
    ERef array = solver.getArrayFromStore(secondaryStore);
    // We need to find the source of the secondary edge (in the same region as this->node),
    // collect the primary path to that node, and update the cursor to the target of the secondary edge
    NodeRef source = solver.getNodeRef(solver.getRoot(array));
    NodeRef target = solver.getNodeRef(solver.getRoot(secondaryStore));
    ERef sourceTerm = array;
    ERef targetTerm = secondaryStore;
    if (traversal.findSecondaryNode(target, index) == secondaryRef) {
        // We got the source and target wrong, target is the node in the same region as this->node, swap
        std::swap(source, target);
        std::swap(sourceTerm, targetTerm);
    }
    assert(traversal.findSecondaryNode(source, index) == secondaryRef);
    ExplanationCursor cursor(traversal, source, sourceTerm);
    this->collectPrimaries(cursor, indices, explanations);
    this->node = target;
    this->term = targetTerm;
    indices.insert(solver.getIndexFromStore(secondaryStore));
}

void ArraySolver::ExplanationCursor::collectPrimaries(ExplanationCursor & destination,
                                                      IndicesCollection & indices,
                                                      ExplanationCollection & explanations) {
    auto count1 = traversal.countPrimaryEdges(this->node);
    auto count2 = traversal.countPrimaryEdges(destination.node);
    while (count1 > count2) {
        this->collectOnePrimary(indices, explanations);
        --count1;
    }
    while (count2 > count1) {
        destination.collectOnePrimary(indices, explanations);
    }
    while (this->node != destination.node) {
        this->collectOnePrimary(indices, explanations);
        destination.collectOnePrimary(indices, explanations);
    }
    if (this->term != destination.term) {
        // Same array node but not same ETerm
        auto explanation = traversal.getSolver().egraph.explainer->explain(this->term, destination.term);
        for (auto literal : explanation) {
            explanations.insert(literal);
        }
    }
}

void ArraySolver::ExplanationCursor::collectOnePrimary(IndicesCollection & indices, ExplanationCollection & explanations) {
    auto const & solver = traversal.getSolver();
    ERef store = traversal.getNode(node).primaryStore;
    ERef source = store;
    ERef target = solver.getArrayFromStore(store);
    if (solver.getNodeRef(solver.getRoot(source)) != this->node) {
        std::swap(source, target);
    }
    assert(solver.getNodeRef(solver.getRoot(source)) == this->node);
    if (this->term != source) {
        auto expl = solver.egraph.explainer->explain(this->term, source);
        for (auto lit : expl) {
            explanations.insert(lit);
        }
    }
    indices.insert(traversal.getSolver().getIndexFromStore(store)); // TODO: Should this be the index or its root?
    this->node = traversal.getNode(this->node).primaryEdge;
    this->term = target;
}
