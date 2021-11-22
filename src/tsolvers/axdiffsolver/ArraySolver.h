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


struct ArrayNode {
    ERef term; // TODO: check if this is needed
    ERef primaryIndex;
    NodeRef primaryEdge;
    NodeRef secondaryEdge;

    ArrayNode(ERef term) : term(term), primaryIndex(ERef_Undef), primaryEdge(NodeRef_Undef), secondaryEdge(NodeRef_Undef) {}
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

    void getConflict(bool b, vec<PtAsgn> & vec) override;

    PtAsgn_reason getDeduction() override;

    void declareAtom(PTRef tr) override;

    Logic & getLogic() override;

    bool isValid(PTRef tr) override;

 /*
 * Internal methods for manipulating weak equivalence graph
 */
private:
    bool checkReadOverWeakEq();

    void merge(ERef);

    void mergeSecondary(NodeRef, NodeRef, Map<ERef, bool, ERefHash> & forbiddenIndices);

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

    NodeRef getNodeRef(ERef root) {
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

    NodeRef getIndexedRepresentative(NodeRef nodeRef, ERef index) {
        ArrayNode & node = getNode(nodeRef);
        if (node.primaryEdge == NodeRef_Undef) { return nodeRef; }
        if (node.primaryIndex != index) { return getIndexedRepresentative(node.primaryEdge, index); }
        if (node.secondaryEdge == NodeRef_Undef) { return nodeRef; }
        return getIndexedRepresentative(node.secondaryEdge, index);
    }

    void print(ostream & out) override;


};


#endif //OPENSMT_ARRAYSOLVER_H
