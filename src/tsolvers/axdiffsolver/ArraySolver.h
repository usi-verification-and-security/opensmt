/*
 *  Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_ARRAYSOLVER_H
#define OPENSMT_ARRAYSOLVER_H

#include "TSolver.h"
#include "Egraph.h"

/*
 * This is an implementation of a theory solver for the theory of arrays with extensionality.
 * It is based on the idea of weak equivalence of arrays as presented in the paper
 * "Weakly Equivalent Arrays" (https://link.springer.com/chapter/10.1007/978-3-319-24246-0_8).
 * The implementation follows from a large part the implementation in SMTInterpol
 * (https://github.com/ultimate-pa/smtinterpol), and differs significantly from the description in the paper.
 *
 * The main data structure is a weak equivalence graph where nodes represent array terms and they are connected by two
 * types of edges:
 *  1. Strong edges, when the terms are equal in the current context (known from Egraph)
 *  2. Weak edges that connects a `store` term with the underlying array term.
 *
 *  In fact, in the implementation, the WE-graph is re-built when the context of strong equivalence changes
 *  (new equality is asserted to Egraph). Thus, the nodes in WE-graph actually represents whole equivalence classes
 *  (not individual terms).
 *
 *  Two arrays are weakly equivalent if they are connected by a path in the WE-graph. If two arrays are weakly equivalent
 *  then they can differ only on finitely many indices. In fact, they can differ only on the indices of store terms
 *  corresponding to the weak edges on the path.
 *
 *  To check consistency of the axioms of the theory of arrays, even finer concept is used: i-weak equivalence
 *  (for index i). Two arrays are i-weakly equivalent if they are connected by a path that does not use index i
 *  (nor any index equivalent to i). If this is the case, then the two arrays must have the same value at index i.
 *  This is captured by first types of lemmas: read-over-weak-eq.
 *  The second types of lemmas are extensionality lemmas which captures that when two arrays actually have
 *  the same elements, then the arrays are equal. This condition is harder to check, but in the end can be
 *  detected from WE-graph: if there is a path between two arrays such that they are weakly CONGRUENT on all store
 *  indices of that path.
 *  Weak congruence is a weaker concept than weak equivalence.
 *  For example, "a" and "(store a i (select a i))" are weakly congruent on i, but not weakly equivalent on i.
 *  The implementation uses a trick how to detect if two arrays are weakly congruent, but then it uses the proper
 *  definition to actually collect the conditions and build the extensionality lemma.
 *
 *  NOTE: The paper distinguishes the cases when element theory is stably infinite or not.
 *  Our implementation for now assumes that the element theory IS stably infinite.
 *
 *  The implementation also assumes that for each store term `(store a i v)` the instance of the identity
 *  select-over-store axiom has been added to the formula: `(= v (select i (store a i v)))`.
 *  This is currently done in the preprocessing.
 */

struct NodeRef { unsigned int id; };
const struct NodeRef NodeRef_Undef = {UINT32_MAX};

inline bool operator==(NodeRef a, NodeRef b) { return a.id == b.id; }
inline bool operator!=(NodeRef a, NodeRef b) { return a.id != b.id; }

struct NodeRefHash {
    uint32_t operator()(NodeRef ref) const {
        return ref.id;
    }
};

/*
 * Node in the WE-graph.
 * It remembers
 * 1. The corresponding array term (root of its equivalence class)
 * 2. Parent node following the primary edge and store term that is the cause of this edge
 * 3. Node following the secondary edge and the store term that is the cause of this edge
 */
struct ArrayNode {
    ERef term {ERef_Undef};
    NodeRef primaryEdge {NodeRef_Undef};
    ERef primaryStore {ERef_Undef};
    NodeRef secondaryEdge {NodeRef_Undef};
    ERef secondaryStore {ERef_Undef};

    explicit ArrayNode(ERef term) : term(term) {}
};

/*
 * Class representing both the theory solver and the WE-graph (MB: This should probably be split)
 */
class ArraySolver : public TSolver {
    Logic & logic;
    Egraph & egraph; // MB: Array solver needs egraph to be able to work with the current (strong) equivalence context

    using Terms = std::set<ERef>;
    Terms arrayTerms;
    Terms storeTerms;
    Terms selectTerms;

    // WE-graph
    std::vector<ArrayNode> nodes;
    std::unordered_map<ERef, NodeRef, ERefHash> rootsMap;

    // Whether or not WE-graph has been built for current context
    bool valid = false;

    vec<PtAsgn> assertedLiterals;

public:
    ArraySolver(Logic & logic, Egraph & egraph, SMTConfig & config);

    ~ArraySolver() = default;

    void clearSolver() override;

    bool assertLit(PtAsgn asgn) override;

    void pushBacktrackPoint() override;

    void popBacktrackPoint() override;

    void popBacktrackPoints(unsigned int i) override;

    TRes check(bool b) override;

    void fillTheoryFunctions(ModelBuilder & builder) const override;

    void computeModel() override;

    void getConflict(vec<PtAsgn> & vec) override;

    void declareAtom(PTRef tr) override;

    Logic & getLogic() override;

    bool isValid(PTRef tr) override;

    void getNewSplits(vec<PTRef> & splits) override;

/*
* Internal methods for traversing weak equivalence graph
*/
private:
    using IndicesCollection = std::unordered_set<ERef, ERefHash>;
    using ExplanationCollection = std::unordered_set<PtAsgn, PtAsgnHash>;

    /*
     * Helper class for traversing the WE-graph.
     * Maybe this should actually properly represent the WE-graph instead of ArraySolver having the WE-graph representation
     */
    class Traversal {
        ArraySolver & solver;
    public:
        Traversal(ArraySolver & solver) : solver(solver) {}

        ArraySolver & getSolver() const { return solver; }

        ArrayNode & getNode(NodeRef ref) const { return solver.getNode(ref); }

        ERef getRoot(ERef term) const { return solver.getRoot(term); }

        NodeRef findSecondaryNode(NodeRef node, ERef index) const;

        unsigned countSecondaryEdges(NodeRef start, ERef index) const;
        unsigned countPrimaryEdges(NodeRef start) const;

        std::unordered_set<ERef, ERefHash> computeStoreIndices(NodeRef, NodeRef, ERef);

        ERef getIndexOfPrimaryEdge(ArrayNode const & node) const {
            return solver.getIndexOfPrimaryEdge(node);
        }
    };

    /*
     * Represents a position in the WE-graph and can move towards the root of (i-)weak equivalence class
     * while collecting store indices encountered.
     */
    class Cursor {
        Traversal traversal;
        NodeRef node;
    public:
        Cursor(ArraySolver & solver, NodeRef node) : traversal(solver), node(node) {}

        NodeRef currentNodeRef() const { return node; }

        ArrayNode & getNode(NodeRef ref) const { return traversal.getNode(ref); }

        unsigned countSecondaryEdges(ERef index) const { return traversal.countSecondaryEdges(node, index); }
        unsigned countPrimaryEdges() const { return traversal.countPrimaryEdges(node); }

        void collectOneSecondary(ERef index, IndicesCollection & indices);
        void collectOverPrimaries(NodeRef destination, IndicesCollection & indices);
    };

    /*
     * Similar to Cursor, but also collects explanations why terms are (weakly or strongly) equivalent.
     */
    class ExplanationCursor {
        Traversal & traversal;
        NodeRef node;
        ERef term;
    public:
        ExplanationCursor(Traversal & traversal, NodeRef node, ERef term) : traversal(traversal), node(node), term(term) {}

        NodeRef getNode() const { return node; }

        void collectPrimaries(ExplanationCursor & destination, IndicesCollection & indices, ExplanationCollection & explanations);
        void collectOnePrimary(IndicesCollection & indices, ExplanationCollection & explanations);
        void collectOneSecondary(ERef index, IndicesCollection & indices, ExplanationCollection & explanations);
    };

 /*
 * Internal methods for bulding weak equivalence graph and computing lemma consequences of the graph
 */
private:
    struct LemmaConditions {
        PTRef equality;
        std::unordered_set<PTRef, PTRefHash> undecidedEqualities;
    };

    std::vector<LemmaConditions> lemmas;

    using SelectsInfo = std::unordered_map<NodeRef, std::unordered_map<ERef, ERef, ERefHash>, NodeRefHash>;
    SelectsInfo selectsInfo;

    PTRef getEquality(ERef lhs, ERef rhs) { return logic.mkEq(egraph.ERefToTerm(lhs), egraph.ERefToTerm(rhs)); }

    bool isFalsified(PTRef equality) const { return this->hasPolarity(equality) and this->getPolarity(equality) == l_False; }
    bool isSatisfied(PTRef equality) const { return this->hasPolarity(equality) and this->getPolarity(equality) == l_True; }

    void computeExplanation(PTRef equality);

    ExplanationCollection readOverWeakEquivalenceConflict(PTRef equality);

    PTRef computeExtensionalityClause(NodeRef n1, NodeRef n2);

    void explainWeakCongruencePath(NodeRef source, NodeRef target, ERef index, ExplanationCollection & explanationCollection);

    ExplanationCollection explainWeakEquivalencePath(ERef array1, ERef array2, ERef index);

    static void merge(ExplanationCollection & main, ExplanationCollection const & other);

    void recordExplanationOfEgraphEquivalence(ERef lhs, ERef rhs, ExplanationCollection & explanationCollection) const;

    void collectLemmaConditions();

    void computeSelectsInfo();

    TRes checkExtensionality();

    void buildWeakEq();

    void merge(ERef);

    void mergeSecondary(NodeRef, NodeRef, ERef, Map<ERef, bool, ERefHash> & forbiddenIndices);

    void clear();

    ERef getArrayFromStore(ERef storeTerm) const {
        PTRef ptref = egraph.ERefToTerm(storeTerm);
        assert(logic.isArrayStore(logic.getSymRef(ptref)));
        PTRef arrayPTerm = logic.getPterm(ptref)[0];
        return egraph.termToERef(arrayPTerm);
    }

    ERef getIndexFromStore(ERef storeTerm) const {
        PTRef ptref = egraph.ERefToTerm(storeTerm);
        assert(logic.isArrayStore(logic.getSymRef(ptref)));
        PTRef indexPTerm = logic.getPterm(ptref)[1];
        return egraph.termToERef(indexPTerm);
    }

    ERef getIndexFromSelect(ERef selectTerm) const {
        PTRef ptref = egraph.ERefToTerm(selectTerm);
        assert(logic.isArraySelect(logic.getSymRef(ptref)));
        PTRef indexPTerm = logic.getPterm(ptref)[1];
        return egraph.termToERef(indexPTerm);
    }

    ERef getArrayFromSelect(ERef selectTerm) const {
        PTRef ptref = egraph.ERefToTerm(selectTerm);
        assert(logic.isArraySelect(logic.getSymRef(ptref)));
        PTRef arrayPTerm = logic.getPterm(ptref)[0];
        return egraph.termToERef(arrayPTerm);
    }

    ERef getRoot(ERef term) const {
        return egraph.getRoot(term);
    }

    ArrayNode & getNode(NodeRef ref) {
        return nodes[ref.id];
    }

    ArrayNode const & getNode(NodeRef ref) const {
        return nodes[ref.id];
    }

    NodeRef getNodeRef(ERef root) const {
        auto it = rootsMap.find(root);
        assert(it != rootsMap.end());
        return it->second;
    }

    void makeWeakRepresentative(NodeRef);

    void makeIndexedWeakRepresentative(NodeRef);

    NodeRef getRepresentative(NodeRef nodeRef) const {
        while (getNode(nodeRef).primaryEdge != NodeRef_Undef) {
            nodeRef = getNode(nodeRef).primaryEdge;
        }
        return nodeRef;
    }

    ERef getIndexOfPrimaryEdge(ArrayNode const & node) const {
        return getIndexFromStore(node.primaryStore);
    }

    NodeRef getIndexedRepresentative(NodeRef nodeRef, ERef index) {
        ArrayNode & node = getNode(nodeRef);
        if (node.primaryEdge == NodeRef_Undef) { return nodeRef; }
        if (getRoot(getIndexOfPrimaryEdge(node)) != index) { return getIndexedRepresentative(node.primaryEdge, index); }
        if (node.secondaryEdge == NodeRef_Undef) { return nodeRef; }
        return getIndexedRepresentative(node.secondaryEdge, index);
    }
};


#endif //OPENSMT_ARRAYSOLVER_H
