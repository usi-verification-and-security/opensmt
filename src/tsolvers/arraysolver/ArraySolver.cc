/*
 *  Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "ArraySolver.h"

#include "TreeOps.h"

#include <numeric>

static SolverDescr descr_ax_solver("Array Solver", "Solver for Theory of Arrays");

ArraySolver::ArraySolver(Logic & logic, Egraph & egraph, SMTConfig & config) :
    TSolver((SolverId) descr_ax_solver, (const char *) descr_ax_solver, config),
    logic(logic),
    egraph(egraph)
    { }

void ArraySolver::clearSolver() {
    clear();
    TSolver::clearSolver();
}

bool ArraySolver::assertLit(PtAsgn literal) {
    if (logic.isEquality(literal.tr)) {
        setPolarity(literal.tr, literal.sgn);
        assertedLiterals.push(literal);
        if (literal.sgn == l_True) { // Strong equivalence context has changed -> reset
            clear();
        } else if (literal.sgn == l_False) {
            // For asserted disequality check current read-over-weak-eq lemmas to see if any is now completely falsified
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
    backtrack_points.push(assertedLiterals.size_());
    TSolver::pushBacktrackPoint();
}

void ArraySolver::popBacktrackPoint() {
    clear();
    assert(backtrack_points.size() > 0);
    auto lastSize = backtrack_points.last();
    backtrack_points.pop();
    while (assertedLiterals.size_() > lastSize) {
        auto lit = assertedLiterals.last();
        assertedLiterals.pop();
        clearPolarity(lit.tr);
    }

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
    for (auto const & lemma : lemmas) {
        if (lemma.undecidedEqualities.empty()) {
            has_explanation = true;
            computeExplanation(lemma.equality);
            return TRes::UNSAT;
        }
    }
    if (complete) {
        if (lemmas.empty()) {
            return checkExtensionality();
        } else {
            for (auto const & lemma : lemmas) {
                auto conflict = readOverWeakEquivalenceConflict(lemma.equality);
                assert(not std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn lit) {
                    return lit.sgn == l_False ? isFalsified(lit.tr) : isSatisfied(lit.tr);
                }));
                vec<PTRef> args;
                args.capacity(conflict.size());
                for (PtAsgn lit : conflict) {
                    assert(lit.sgn != l_Undef);
                    // MB: To obtain lemma, we need to negate the literals of the conflict
                    PTRef arg = lit.sgn == l_True ? logic.mkNot(lit.tr) : lit.tr;
                    args.push(arg);
                }
                splitondemand.push(logic.mkOr(std::move(args)));
            }
        }
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

void ArraySolver::declareAtom(PTRef tr) {
    class TermCollectorConfig : public DefaultVisitorConfig {
        Logic const & logic;
        ArraySolver::Terms & arrayTerms;
        ArraySolver::Terms & storeTerms;
        ArraySolver::Terms & selectTerms;
        Egraph const & egraph;

    public:
        TermCollectorConfig(Logic const & logic, Terms & arrayTerms, Terms & storeTerms, Terms & selectTerms, Egraph const & egraph)
        : logic(logic), arrayTerms(arrayTerms), storeTerms(storeTerms), selectTerms(selectTerms), egraph(egraph) {}

        void visit(PTRef term) override {
            if (logic.isArraySort(logic.getSortRef(term))) {
                ERef eref = egraph.termToERef(term);
                arrayTerms.insert(eref);
                if (logic.isArrayStore(term)) {
                    storeTerms.insert(eref);
                }
            } else if (logic.isArraySelect(term)) {
                ERef eref = egraph.termToERef(term);
                selectTerms.insert(eref);
            }
        }
    };

    TermCollectorConfig config(logic, arrayTerms, storeTerms, selectTerms, egraph);
    TermVisitor<TermCollectorConfig>(logic, config).visit(tr);

    if (logic.isEquality(tr)) {
        setInformed(tr);
    }
}

Logic & ArraySolver::getLogic() {
    return logic;
}

bool ArraySolver::isValid(PTRef tr) {
    return egraph.isValid(tr);
}

void ArraySolver::getNewSplits(vec<PTRef> & splits) {
    splitondemand.copyTo(splits);
    splitondemand.clear();
}


/*
 * Internal methods for manipulating weak equivalence graph
 */

void ArraySolver::makeIndexedWeakRepresentative(NodeRef nodeRef) {
    ArrayNode & node = getNode(nodeRef);
    NodeRef secondaryRef = node.secondaryEdge;
    if (secondaryRef != NodeRef_Undef) {
        if (getRoot(getIndexOfPrimaryEdge(secondaryRef)) != getRoot(getIndexOfPrimaryEdge(nodeRef))) {
            node.secondaryEdge = getNode(secondaryRef).primaryEdge;
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
        // Make representative for i-weak equivalence class
        // Information about primary store is needed in "makeIndexedWeakRepresentative"!
        makeIndexedWeakRepresentative(nodeRef);
        node.primaryEdge = NodeRef_Undef;
        node.primaryStore = ERef_Undef;
    }
}

void ArraySolver::merge(ERef storeTerm) {
    assert(logic.isArrayStore(egraph.ERefToTerm(storeTerm)));
    ERef arrayTerm = getArrayFromStore(storeTerm);
    ERef indexTerm = getRoot(getIndexFromStore(storeTerm));
    NodeRef arrayNode = getNodeRef(getRoot(arrayTerm));
    NodeRef storeNode = getNodeRef(getRoot(storeTerm));
    if (arrayNode == storeNode) { return; }
    makeWeakRepresentative(arrayNode);
    if (getRepresentative(storeNode) == arrayNode) {
        mergeSecondary(storeNode, arrayNode, storeTerm, std::unordered_set<ERef,ERefHash>({indexTerm}));
    } else {
        // new primary edge
        getNode(arrayNode).primaryEdge = storeNode;
        getNode(arrayNode).primaryStore = storeTerm;
    }
}

void ArraySolver::mergeSecondary(NodeRef nodeRef, NodeRef root, ERef store, std::unordered_set<ERef,ERefHash> && forbiddenIndices) {
    if (nodeRef == root) { return; }
    ArrayNode & node = getNode(nodeRef);
    ERef primaryIndex = getRoot(getIndexOfPrimaryEdge(nodeRef));
    assert(getRoot(primaryIndex) == primaryIndex);
    if (forbiddenIndices.find(primaryIndex) == forbiddenIndices.end() and getIndexedRepresentative(nodeRef, primaryIndex) != root) {
        makeIndexedWeakRepresentative(nodeRef);
        node.secondaryEdge = root;
        node.secondaryStore = store;
    }
    forbiddenIndices.insert(primaryIndex);
    mergeSecondary(node.primaryEdge, root, store, std::move(forbiddenIndices));
}

/*
 * Build the WE-graph for current context and compute read-over-weak-eq lemmas that need to be valid.
 */
void ArraySolver::buildWeakEq() {
    assert(not valid);
    assert(nodes.empty() and rootsMap.empty() and lemmas.empty());
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
    lemmas = collectLemmaConditions(logic);
    valid = true;
}

void ArraySolver::computeSelectsInfo() {
    for (ERef select : selectTerms) {
        ERef index = getRoot(getIndexFromSelect(select));
        NodeRef arrayNode = getNodeRef(getRoot(getArrayFromSelect(select)));
        NodeRef weakIRepresentative = getIndexedRepresentative(arrayNode, index);
        selectsInfo[weakIRepresentative].insert({index, select});
    }
}

namespace {
struct ExtensionalityInfo {
    using IndexValueMap = std::unordered_map<ERef, ERef, ERefHash>;

    NodeRef weakEqRoot;
    std::unordered_map<ERef, NodeRef, ERefHash> weakIRoots;
    IndexValueMap indexValueMap;

    void erase(ERef index) {
        indexValueMap.erase(index);
        weakIRoots.erase(index);
    }
};

bool operator==(ExtensionalityInfo const & first, ExtensionalityInfo const & second) {
    if (first.weakEqRoot != second.weakEqRoot) { return false; }
    if (first.weakIRoots.size() != second.weakIRoots.size()) { return false; }
    if (first.indexValueMap.size() != second.indexValueMap.size()) { return false; }
    return first.weakIRoots == second.weakIRoots and first.indexValueMap == second.indexValueMap;
}

struct ExtensionalityInfoHash {
    uint32_t operator()(ExtensionalityInfo const & info) const {
        std::hash<uint32_t> hasher{};
        uint32_t res = hasher(info.weakEqRoot.id);
        res = std::accumulate(info.weakIRoots.begin(), info.weakIRoots.end(), res, [&](uint32_t acc, auto const & entry) {
            return acc ^ hasher(entry.first.x + entry.second.id);
        });
        res = std::accumulate(info.indexValueMap.begin(), info.indexValueMap.end(), res, [&](uint32_t acc, auto const & entry) {
            return acc ^ hasher(entry.first.x + entry.second.x);
        });
        return res;
    }
};

}

TRes ArraySolver::checkExtensionality() {
    if (selectsInfo.empty()) { computeSelectsInfo(); }

    std::unordered_map<NodeRef, ExtensionalityInfo, NodeRefHash> extensionalityInfos;
    std::unordered_map<ExtensionalityInfo, NodeRef, ExtensionalityInfoHash> inverseExtensionalityInfos;
    vec<opensmt::pair<NodeRef, NodeRef>> equalitiesToPropagate;

    vec<NodeRef> queue;
    queue.capacity(rootsMap.size());
    for (auto const & entry : rootsMap) {
        queue.push(entry.second);
    }

    while (queue.size() > 0) {
        NodeRef const current = queue.last();
        if (extensionalityInfos.find(current) != extensionalityInfos.end()) {
            queue.pop();
            continue;
        }
        ArrayNode const & node = getNode(current);
        if (node.primaryEdge != NodeRef_Undef and extensionalityInfos.find(node.primaryEdge) == extensionalityInfos.end()) {
            queue.push(node.primaryEdge);
            continue;
        }
        queue.pop();
        ExtensionalityInfo extensionalityInfo;
        NodeRef const weakEqRoot = getRepresentative(current);
        if (current == weakEqRoot) { // Root of weak-eq class
            extensionalityInfo.weakEqRoot = current;
            auto it = selectsInfo.find(current);
            if (it != selectsInfo.end()) {
                auto const & selects = it->second;
                for (auto && [index, value] : selects) {
                    extensionalityInfo.indexValueMap.insert({index, getRoot(value)});
                }
            }
        } else { // not weak-eq root
            ERef primaryIndex = getRoot(getIndexFromStore(node.primaryStore));
            assert(extensionalityInfos.find(node.primaryEdge) != extensionalityInfos.end());
            // Select are the same as primary parent, except possibly at primary index
            extensionalityInfo = extensionalityInfos.at(node.primaryEdge);
            extensionalityInfo.erase(primaryIndex);

            NodeRef weakIRoot = getIndexedRepresentative(current, primaryIndex);
            auto selectsInfoIt = selectsInfo.find(weakIRoot);
            if (selectsInfoIt != selectsInfo.end()) {
                auto const & weakIRootSelects = selectsInfoIt->second;
                auto it = weakIRootSelects.find(primaryIndex);
                if (it != weakIRootSelects.end()) {
                    ERef valueAtPrimaryIndex = getRoot(it->second);
                    extensionalityInfo.indexValueMap.insert({primaryIndex, valueAtPrimaryIndex});
                } else {
                    extensionalityInfo.weakIRoots.insert({primaryIndex, weakIRoot});
                }
            } else {
                extensionalityInfo.weakIRoots.insert({primaryIndex, weakIRoot});
            }
        }

        auto it = inverseExtensionalityInfos.find(extensionalityInfo);
        if (it != inverseExtensionalityInfos.end()) {
            equalitiesToPropagate.push({current, it->second});
            it->second = current;
        } else {
            inverseExtensionalityInfos.insert({extensionalityInfo, current});
        }
        extensionalityInfos.insert({current, std::move(extensionalityInfo)});
    }

    for (auto const & entry : equalitiesToPropagate) {
        PTRef extensionalityClause = computeExtensionalityClause(entry.first, entry.second);
        assert(logic.isOr(extensionalityClause));
        // TODO: handle conflicts better: We pass literals twice now.
        // TODO: looks like the above graph traversal could be terminated early if a clause is all-falsified
        Pterm & literals = logic.getPterm(extensionalityClause);
        bool allFalsified = std::all_of(literals.begin(), literals.end(),
                                        [this](PTRef lit) {
                                            bool negated = logic.isNot(lit);
                                            PTRef atom = negated ? logic.getPterm(lit)[0] : lit;
                                            assert(logic.isEquality(atom));
                                            return negated ? isSatisfied(atom) : isFalsified(atom);
                                        });
        if (allFalsified) {
            has_explanation = true;
            explanation.clear();
            for (PTRef lit : literals) {
                if (logic.isNot(lit)) {
                    explanation.push({logic.getPterm(lit)[0], l_True});
                } else {
                    explanation.push({lit, l_False});
                }
            }
            splitondemand.clear();
            return TRes::UNSAT;
        }
        splitondemand.push(extensionalityClause);
    }
    return TRes::SAT;
}

PTRef ArraySolver::computeExtensionalityClause(NodeRef n1, NodeRef n2) {
    Traversal traversal(*this);
    ExplanationCollection explanationCollection;
    IndicesCollection indicesCollection;
    ExplanationCursor source(traversal, n1, getNode(n1).term);
    ExplanationCursor destination(traversal, n2, getNode(n2).term);
    source.collectPrimaries(destination, indicesCollection, explanationCollection);
    for (ERef index : indicesCollection) {
        explainWeakCongruencePath(explanationCollection, n1, n2, index);
    }

    vec<PTRef> args;
    args.capacity(explanationCollection.size());
    for (PtAsgn lit : explanationCollection) {
        // Explanation collection holds the antecedent for n1 and n2 being equal
        // For the clause we negate the antecedent literals
        assert(lit.sgn != l_Undef);
        args.push(lit.sgn == l_True ? logic.mkNot(lit.tr) : lit.tr);
    }
    args.push(getEquality(getNode(n1).term, getNode(n2).term, logic));

    return logic.mkOr(std::move(args));
}

/*
 * Somewhat naive way how to compute all read-over-weak-eq lemmas for current WE-graph.
 *
 * Every pair of selects with weakly-equivalent array terms needs a corresponding lemma.
 */
std::vector<ArraySolver::LemmaConditions> ArraySolver::collectLemmaConditions(Logic & logic) const {
    std::unordered_map<ERef, vec<ERef>, ERefHash> indicesToSelects;
    for (ERef select : selectTerms) {
        ERef root = getRoot(getIndexFromSelect(select));
        indicesToSelects[root].push(select);
    }
    std::vector<LemmaConditions> newLemmas;
    for (auto const & [index, selects] : indicesToSelects) {
        if (selects.size() < 2) { continue; }
        // TODO: Figure out better way how to compute all candidates for lemmas
        for (auto first : selects) {
            ERef firstRoot = getRoot(first);
            for (auto secondIt = selects.begin(); *secondIt != first; ++secondIt) {
                ERef second = *secondIt;
                if (firstRoot == getRoot(second)) { continue; } // The selects are already the same, no lemma needed
                NodeRef arrayFirst = getNodeRef(getRoot(getArrayFromSelect(first)));
                NodeRef arraySecond = getNodeRef(getRoot(getArrayFromSelect(second)));
                if (arrayFirst == arraySecond or getIndexedRepresentative(arrayFirst, index) == getIndexedRepresentative(arraySecond, index)) {
                    std::unordered_set<PTRef, PTRefHash> undecidedEqualities;
                    PTRef equalityOfSelects = getEquality(first, second, logic);
                    if (not isFalsified(equalityOfSelects)) {
                        assert(not isSatisfied(equalityOfSelects));
                        undecidedEqualities.insert(equalityOfSelects);
                    }
                    auto storeIndices = Traversal(*this).computeStoreIndices(arrayFirst, arraySecond, index);
                    for (ERef storeIndex : storeIndices) {
                        assert(storeIndex != index);
                        PTRef equalityOfIndices = getEquality(index, storeIndex, logic);
                        if (not isFalsified(equalityOfIndices)) {
                            assert(not isSatisfied(equalityOfIndices));
                            undecidedEqualities.insert(equalityOfIndices);
                        }
                    }
                    newLemmas.emplace_back(equalityOfSelects, std::move(undecidedEqualities));
                }
            }
        }
    }
    return newLemmas;
}

/*
 * Collect the store indices on the path from array1 to array2 using only indices different from index.
 */
std::unordered_set<ERef, ERefHash> ArraySolver::Traversal::computeStoreIndices(NodeRef array1, NodeRef array2, ERef index) const {
    assert(index == getRoot(index));
    Cursor cursor1(getSolver(), array1);
    Cursor cursor2(getSolver(), array2);
    std::unordered_set<ERef, ERefHash> indices;
    auto steps1 = cursor1.countSecondaryEdges(index);
    auto steps2 = cursor2.countSecondaryEdges(index);
    while (steps1 > steps2) {
        cursor1.collectOneSecondary(indices, index);
        --steps1;
    }
    while (steps2 > steps1) {
        cursor2.collectOneSecondary(indices, index);
        --steps2;
    }
    while (findSecondaryNode(cursor1.getCurrentNodeRef(), index) != findSecondaryNode(cursor2.getCurrentNodeRef(), index)) {
        cursor1.collectOneSecondary(indices, index);
        cursor2.collectOneSecondary(indices, index);
    }
    cursor1.collectOverPrimaries(indices, cursor2.getCurrentNodeRef());
    return indices;
}

void ArraySolver::computeExplanation(PTRef equality) {
    auto conflictExplanation = readOverWeakEquivalenceConflict(equality);
    has_explanation = true;
    explanation.clear();
    for (auto lit : conflictExplanation) {
        explanation.push(lit);
    }
}

/*
 * Compute the literals representing the negation of a read-over-weak-eq lemma, i.e., the conflict, for the given
 * equality in the current context.
 */
ArraySolver::ExplanationCollection ArraySolver::readOverWeakEquivalenceConflict(PTRef equality) {
    assert(logic.isEquality(equality));
    PTRef lhs = logic.getPterm(equality)[0];
    PTRef rhs = logic.getPterm(equality)[1];
    assert(logic.isArraySelect(lhs));
    assert(logic.isArraySelect(rhs));
    ERef array1 = egraph.termToERef(logic.getPterm(lhs)[0]);
    ERef array2 = egraph.termToERef(logic.getPterm(rhs)[0]);
    ERef index1 = egraph.termToERef(logic.getPterm(lhs)[1]);
    ERef index2 = egraph.termToERef(logic.getPterm(rhs)[1]);

    // collect literals explaining why array1 is weakly equivalent to array2
    ERef root1 = getRoot(index1);
    auto lemma = explainWeakEquivalencePath(array1, array2, root1);
    // collect literals explaining why index1 is equivalent to index2 in Egraph
    if (index1 != index2) {
        recordExplanationOfEgraphEquivalence(lemma, index1, index2);
    }
    // collect literals explaining why index1 is equivalent to its root
    if (root1 != index1) {
        recordExplanationOfEgraphEquivalence(lemma, index1, root1);
    }
    // add literal asserting that the selects are not equal
    lemma.insert({equality, l_False});
    return lemma;
}

/*
 * Explain why the two input arrays are weakly equivalent on index "index".
 * Since they are weakly equivalent on "index", the selects "array1[index]" and "array2[index]" must have the same value.
 *
 * @returns The collection of literals that guarantees the i-weak equivalence
 */
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
        --count1;
    }
    while (count2 > count1) {
        cursor2.collectOneSecondary(index, storeIndices, explanations);
        --count2;
    }
    while (traversal.findSecondaryNode(cursor1.getCurrentNodeRef(), index) != traversal.findSecondaryNode(cursor2.getCurrentNodeRef(), index)) {
        cursor1.collectOneSecondary(index, storeIndices, explanations);
        cursor2.collectOneSecondary(index, storeIndices, explanations);
    }
    cursor1.collectPrimaries(cursor2, storeIndices, explanations);
    for (ERef storeIndex : storeIndices) {
        PTRef eq = getEquality(storeIndex, index, logic);
        if (eq != logic.getTerm_false()) {
            explanations.insert(PtAsgn(eq, l_False));
        }
    }
    return explanations;
}

void ArraySolver::clear() {
    lemmas.clear();
    selectsInfo.clear();
    nodes.clear();
    rootsMap.clear();
    valid = false;

    has_explanation = false;
    explanation.clear();
}

/*
 * Collect the explanation from Egraph why two terms are equivalent
 */
void ArraySolver::recordExplanationOfEgraphEquivalence(ExplanationCollection & explanationCollection, ERef lhs, ERef rhs) const {
    assert(getRoot(lhs) == getRoot(rhs));
    auto egraphExplanation = egraph.explainer->explain(lhs, rhs);
    for (PtAsgn lit : egraphExplanation) {
        explanationCollection.insert(lit);
    }
}

void ArraySolver::explainWeakCongruencePath(ExplanationCollection & explanationCollection, NodeRef source, NodeRef target, ERef index) {
    ERef indexRoot = getRoot(index);
    if (index != indexRoot) {
        recordExplanationOfEgraphEquivalence(explanationCollection, index, indexRoot);
        index = indexRoot;
    }
    NodeRef sourceRepresentative = getIndexedRepresentative(source, index);
    NodeRef targetRepresentative = getIndexedRepresentative(target, index);
    if (sourceRepresentative == targetRepresentative) {
        explanationCollection.merge(explainWeakEquivalencePath(getNode(source).term, getNode(target).term, index));
        return;
    }
    assert(selectsInfo.count(sourceRepresentative) > 0);
    assert(selectsInfo.count(targetRepresentative) > 0);

    ERef sourceSelect = selectsInfo.find(sourceRepresentative)->second.at(index);
    ERef targetSelect = selectsInfo.find(targetRepresentative)->second.at(index);

    auto explainPathToSelect = [&](ERef select, ERef arrayTerm) {
        ERef selectArray = getArrayFromSelect(select);
        explanationCollection.merge(explainWeakEquivalencePath(arrayTerm, selectArray, index));
        recordExplanationOfEgraphEquivalence(explanationCollection, index, getIndexFromSelect(select));
    };

    explainPathToSelect(sourceSelect, getNode(source).term);
    explainPathToSelect(targetSelect, getNode(target).term);

    assert(getRoot(sourceSelect) == getRoot(targetSelect));
    if (sourceSelect != targetSelect) {
        recordExplanationOfEgraphEquivalence(explanationCollection, sourceSelect, targetSelect);
    }
}

unsigned int ArraySolver::Traversal::countSecondaryEdges(NodeRef start, ERef index) const {
    assert(getRoot(index) == index);
    unsigned count = 0;
    NodeRef currentRef = start;
    while (getNode(currentRef).primaryEdge != NodeRef_Undef) {
        auto const & currentNode = getNode(currentRef);
        auto primaryIndex = getRoot(solver.getIndexOfPrimaryEdge(currentRef));
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
    while (getNode(nodeRef).primaryEdge != NodeRef_Undef and getRoot(getIndexOfPrimaryEdge(nodeRef)) != index) {
        nodeRef = getNode(nodeRef).primaryEdge;
    }
    return nodeRef;
}

void ArraySolver::Cursor::collectOneSecondary(IndicesCollection & indices, ERef index) {
    NodeRef secondaryNode = traversal.findSecondaryNode(currentNodeRef, index);
    ERef store = getNode(secondaryNode).secondaryStore;
    auto & solver = traversal.getSolver();
    ERef array = solver.getArrayFromStore(store);
    NodeRef arrayNode = solver.getNodeRef(solver.getRoot(array));
    NodeRef storeNode = solver.getNodeRef(solver.getRoot(store));
    if (traversal.findSecondaryNode(arrayNode, index) == secondaryNode) {
        collectOverPrimaries(indices, arrayNode);
        currentNodeRef = storeNode;
    } else if (traversal.findSecondaryNode(storeNode, index) == secondaryNode) {
        collectOverPrimaries(indices, storeNode);
        currentNodeRef = arrayNode;
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

void ArraySolver::Cursor::collectOverPrimaries(IndicesCollection & indices, NodeRef destination) {
    // compute the steps to the common root
    auto steps1 = countPrimaryEdges();
    auto steps2 = Cursor(traversal.getSolver(),destination).countPrimaryEdges();
    // if one needs more step than the other, follow the primary edges until the steps equal
    while (steps1 > steps2) {
        indices.insert(traversal.getIndexOfPrimaryEdge(currentNodeRef));
        currentNodeRef = getNode(currentNodeRef).primaryEdge;
        steps1--;
    }
    while (steps2 > steps1) {
        indices.insert(traversal.getIndexOfPrimaryEdge(destination));
        destination = getNode(destination).primaryEdge;
        steps2--;
    }
    // now follow the primary edge from both nodes until the common ancestor is found
    while (currentNodeRef != destination) {
        indices.insert(traversal.getIndexOfPrimaryEdge(currentNodeRef));
        indices.insert(traversal.getIndexOfPrimaryEdge(destination));
        currentNodeRef = getNode(currentNodeRef).primaryEdge;
        destination = getNode(destination).primaryEdge;
    }
}

void ArraySolver::ExplanationCursor::collectOneSecondary(
    ERef index,
    IndicesCollection & indices,
    ExplanationCollection & explanations) {

    NodeRef secondaryRef = traversal.findSecondaryNode(currentNode.ref, index);
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
    collectPrimaries(cursor, indices, explanations);
    currentNode = {target, targetTerm};
    indices.insert(solver.getIndexFromStore(secondaryStore));
}

void ArraySolver::ExplanationCursor::collectPrimaries(ExplanationCursor & destination,
                                                      IndicesCollection & indices,
                                                      ExplanationCollection & explanations) {
    auto count1 = traversal.countPrimaryEdges(currentNode.ref);
    auto count2 = traversal.countPrimaryEdges(destination.currentNode.ref);
    while (count1 > count2) {
        collectOnePrimary(indices, explanations);
        --count1;
    }
    while (count2 > count1) {
        destination.collectOnePrimary(indices, explanations);
        --count2;
    }
    while (currentNode.ref != destination.currentNode.ref) {
        collectOnePrimary(indices, explanations);
        destination.collectOnePrimary(indices, explanations);
    }
    if (currentNode.term != destination.currentNode.term) {
        // Same array node but not same Enode
        traversal.getSolver().recordExplanationOfEgraphEquivalence(explanations, currentNode.term, destination.currentNode.term);
    }
}

void ArraySolver::ExplanationCursor::collectOnePrimary(IndicesCollection & indices, ExplanationCollection & explanations) {
    auto const & solver = traversal.getSolver();
    ERef store = traversal.getNode(currentNode.ref).primaryStore;
    ERef source = store;
    ERef target = solver.getArrayFromStore(store);
    if (solver.getNodeRef(solver.getRoot(source)) != currentNode.ref) {
        std::swap(source, target);
    }
    assert(solver.getNodeRef(solver.getRoot(source)) == currentNode.ref);
    if (currentNode.term != source) {
        solver.recordExplanationOfEgraphEquivalence(explanations, currentNode.term, source);
    }
    indices.insert(traversal.getSolver().getIndexFromStore(store)); // MB: This must be the real index, not its root!
    currentNode = {traversal.getNode(currentNode.ref).primaryEdge, target};
}
