//
// Created by Martin Blicha on 22.11.21.
//

#ifndef OPENSMT_ARRAYSOLVER_H
#define OPENSMT_ARRAYSOLVER_H

#include "TSolver.h"
#include "Egraph.h"

struct NodeRef { unsigned int id; };
const struct NodeRef NodeRef_Undef = {UINT32_MAX};

inline bool operator==(NodeRef a, NodeRef b) { return a.id == b.id; }
inline bool operator!=(NodeRef a, NodeRef b) { return a.id != b.id; }

struct NodeRefHash {
    uint32_t operator()(NodeRef ref) const {
        return ref.id;
    }
};


struct ArrayNode {
    ERef term {ERef_Undef};
    ERef primaryStore {ERef_Undef};
    NodeRef primaryEdge {NodeRef_Undef};
    NodeRef secondaryEdge {NodeRef_Undef};
    ERef secondaryStore {ERef_Undef};

    explicit ArrayNode(ERef term) : term(term) {}
};

class ArraySolver : public TSolver {
    Logic & logic;
    Egraph & egraph;

    using Terms = std::set<ERef>;
    Terms arrayTerms;
    Terms storeTerms;
    Terms selectTerms;

    std::vector<ArrayNode> nodes;
    std::unordered_map<ERef, NodeRef, ERefHash> rootsMap;

    bool valid = false;


public:
    ArraySolver(Logic & logic, Egraph & egraph, SMTConfig & config);

    ~ArraySolver() override;

    void clearSolver() override;

    bool assertLit(PtAsgn asgn) override;

    void pushBacktrackPoint() override;

    void popBacktrackPoint() override;

    void popBacktrackPoints(unsigned int i) override;

    TRes check(bool b) override;

    void fillTheoryFunctions(ModelBuilder & builder) const override;

    void computeModel() override;

    void getConflict(vec<PtAsgn> & vec) override;

    PtAsgn_reason getDeduction() override;

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
 * Internal methods for manipulating weak equivalence graph
 */
private:
    struct LemmaConditions {
        PTRef equality;
        std::unordered_set<PTRef, PTRefHash> undecidedEqualities;
    };

    std::vector<LemmaConditions> lemmas;

    using SelectsInfo = std::unordered_map<NodeRef, std::unordered_map<ERef, ERef, ERefHash>, NodeRefHash>;
    SelectsInfo selectsInfo;

    PTRef getEquality(ERef lhs, ERef rhs);

    bool isFalsified(PTRef equality);
    bool isSatisfied(PTRef equality);

    void computeExplanation(PTRef equality);

    ExplanationCollection readOverWeakEquivalenceLemma(PTRef equality);

    PTRef computeExtensionalityClause(NodeRef n1, NodeRef n2);

    void explainWeakCongruencePath(NodeRef source, NodeRef target, ERef index, ExplanationCollection & explanationCollection);

    ExplanationCollection explainWeakEquivalencePath(ERef array1, ERef array2, ERef index);

    // Helper
    static void merge(ArraySolver::ExplanationCollection & main, ExplanationCollection const & other);

    void recordExplanationOfEgraphEquivalence(ERef lhs, ERef rhs, ExplanationCollection & explanationColletion) const;

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

    NodeRef getRepresentative(NodeRef nodeRef) {
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
