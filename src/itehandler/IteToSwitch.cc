//
// Created by prova on 04.08.20.
//

#include "IteToSwitch.h"
#include "Logic.h"

ite::Node::Node(PTRef term, PTRef cond, NodeRef true_node, NodeRef false_node, uint32_t id)
    : id(id)
    , type(cond != PTRef_Undef ? static_cast<bool>(NodeType::inner) : static_cast<bool>(NodeType::leaf))
    , term(term)
{
    if (cond != PTRef_Undef) {
        // a leaf node.
        setCond(cond);
        setTrueChild(true_node);
        setFalseChild(false_node);
    }
}

ite::NodeRef ite::Dag::newNode(PTRef val) {
    return newNode(val, PTRef_Undef, NodeRef_Undef, NodeRef_Undef);
}

ite::NodeRef ite::Dag::newNode(PTRef tr, PTRef cond, ite::NodeRef true_node, ite::NodeRef false_node)
{
    assert(not nodes.has(tr));
    nodeRefs.push(na.alloc(tr, cond, true_node, false_node));
    nodes.insert(tr, nodeRefs.last());
    return nodeRefs.last();
}

void ite::Dag::annotateWithParentInfo(PTRef root_tr) {
    NodeRef root = getNode(root_tr);
    vec<NodeRef> queue;
    vec<type> flag;
    flag.growTo(na.getNumNodes());
    parents[root] = ParentSet();
    queue.push(root);
    while (queue.size() != 0) {
        NodeRef el_r = queue.last();
        const Node &el = na[el_r];
        if (flag[el.getId()] == type::black) {
            queue.pop();
            continue;
        }
        flag[el.getId()] = type::gray;

        bool unprocessed_children = false;

        for (lbool childPolarity : { l_False, l_True }) {
            NodeRef child = childPolarity == l_False ? el.getFalseChild() : el.getTrueChild();
            if (child != NodeRef_Undef) {
                parents[child].insert({el_r, childPolarity});

                if (flag[na[child].getId()] == type::white) {
                    unprocessed_children = true;
                    queue.push(child);
                }
            }
            else {
                leaves.insert(el_r);
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[el.getId()] = type::black;
        queue.pop();
    }
}

ite::Dag ite::Dag::getReachableSubGraph(const Logic &logic, PTRef root) {
    Dag dag;
    vec<NodeRef> queue;
    vec<type> flag;
    flag.growTo(na.getNumNodes());
    NodeRef rootNode = nodes[root];
    queue.push(rootNode);

    while (queue.size() > 0) {
        NodeRef el_r = queue.last();
        const Node &el = na[el_r];
        if (flag[el.getId()] == type::black) {
            queue.pop();
            continue;
        }

        flag[el.getId()] = type::gray;
        bool unprocessed_children = false;
        for (NodeRef child : {el.getFalseChild(), el.getTrueChild()}) {
            if (child != NodeRef_Undef && flag[na[child].getId()] == type::white) {
                queue.push(child);
                unprocessed_children = true;
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[el.getId()] = type::black;

        queue.pop();

        PTRef term = el.getTerm();
        if (logic.isIte(term)) {
            assert(na[el_r].getTrueChild() != NodeRef_Undef);
            assert(na[el_r].getFalseChild() != NodeRef_Undef);
            NodeRef true_node = dag.getNodeOrCreateLeafNode(na[na[el_r].getTrueChild()].getTerm());
            NodeRef false_node = dag.getNodeOrCreateLeafNode(na[na[el_r].getFalseChild()].getTerm());
            dag.createAndStoreNode(term, na[el_r].getCond(), true_node, false_node);
        } else {
            for (int i = 0; i < logic.getPterm(term).size(); i++) {
                PTRef c = logic.getPterm(term)[i];
                if (logic.isIte(c) and isTopLevelIte(c)) {
                    dag.addTopLevelIte(c);
                }
            }
        }
    }
    return dag;
}

vec<ite::CondValPair> ite::Dag::getCondValPairs(Logic& logic) const {
    // Reverse traversal starting from leaves
    std::map<NodeRef, PTRef> dagNodeToPTRef;
    vec<NodeRef> queue;
    for (auto root : leaves) {
        queue.push(root);
    }
    vec<type> flag;
    flag.growTo(na.getNumNodes());
    vec<CondValPair> switches;

    while (queue.size() != 0) {
        NodeRef el_r = queue.last();
        const Node &el = na[el_r];

        if (flag[el.getId()] == type::black) {
            queue.pop();
            continue;
        }

        bool unprocessed_parents = false;
        for (const auto &parentAndPolarity : parents.at(el_r)) {
            auto parent = parentAndPolarity.nr;
            if (flag[na[parent].getId()] == type::white) {
                flag[na[parent].getId()] = type::gray;
                queue.push(parent);
                unprocessed_parents = true;
            }
        }

        if (unprocessed_parents) {
            continue;
        }

        flag[el.getId()] = type::black;
        queue.pop();

        if (dagNodeToPTRef.find(el_r) == dagNodeToPTRef.end()) {
            auto &myParents = parents.at(el_r);
            vec<PTRef> parentConditions;
            if (myParents.empty()) {
                parentConditions.push(logic.getTerm_true());
            } else {
                for (auto &nodeAndPolarity : myParents) {
                    PTRef cond = na[nodeAndPolarity.nr].getCond();
                    lbool pol = nodeAndPolarity.sign;
                    PTRef parentCondition = dagNodeToPTRef.at(nodeAndPolarity.nr);
                    PTRef edgeCondition = pol == l_True ? cond : logic.mkNot(cond);
                    parentConditions.push(logic.mkAnd(parentCondition, edgeCondition));
                }
            }

            PTRef pathCondition = logic.mkOr(std::move(parentConditions));
            dagNodeToPTRef[el_r] = pathCondition;

            if (el.isLeaf()) {
                // A value node
                switches.push_m(CondValPair(pathCondition, el.getVal()));
            }
        }
    }

    return switches;
}

ite::Dag IteToSwitch::constructIteDag(PTRef root, const Logic &logic) {

    ite::Dag dag;

    vec<PTRef> queue;
    vec<type> flag;
    flag.growTo(logic.getNumberOfTerms());

    if (logic.isIte(root)) {
        dag.addTopLevelIte(root);
    }

    queue.push(root);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        const Pterm &t = logic.getPterm(tr);
        auto index = Idx(t.getId());
        if (flag[index] == ite::type::black) {
            queue.pop();
            continue;
        }

        flag[index] = type::gray;

        bool unprocessed_children = false;

        for (int i = 0; i < t.size(); i++) {
            auto childIndex = Idx(logic.getPterm(t[i]).getId());
            if (flag[childIndex] == type::white) {
                queue.push(t[i]);
                unprocessed_children = true;
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[index] = type::black;

        queue.pop();

        if (logic.isIte(tr)) {

            dag.addItePTRef(tr);

            const Pterm &ite = logic.getPterm(tr);
            PTRef cond_tr = ite[0];
            PTRef true_tr = ite[1];
            PTRef false_tr = ite[2];
            {
                ite::NodeRef true_node = dag.getNodeOrCreateLeafNode(true_tr);
                ite::NodeRef false_node = dag.getNodeOrCreateLeafNode(false_tr);
                assert(logic.hasSortBool(cond_tr));
                dag.createAndStoreNode(tr, cond_tr, true_node, false_node);
            }
            if (logic.isIte(cond_tr) and !dag.isTopLevelIte(cond_tr)) {
                dag.addTopLevelIte(cond_tr); // The (boolean) ites at condition are always top-level
            }

        } else { // not Ite
            for (int i = 0; i < t.size(); i++) {
                if (logic.isIte(t[i]) and !dag.isTopLevelIte(t[i])) {
                    // Term t[i] is an ite which appears as a child of a non-ite.
                    // We store this term for an expansion into a switch.
                    dag.addTopLevelIte(t[i]);
                }
            }
        }
    }
    return dag;
}

void IteToSwitch::constructSwitches() {
    const vec<PTRef> & ites = iteDag.getTopLevelItes();

    for (auto tl_ite : ites) {
        PTRef switch_tr = makeSwitch(tl_ite);
        switches.push(switch_tr);
    }
}

PTRef IteToSwitch::makeSwitch(PTRef root) {
    ite::Dag dag = iteDag.getReachableSubGraph(logic, root);
    dag.annotateWithParentInfo(root);
    vec<ite::CondValPair> root_switches = dag.getCondValPairs(logic);
    vec<PTRef> cases;
    for (auto condVal : root_switches) {
        cases.push(logic.mkImpl(condVal.cond, logic.mkEq(root, condVal.val)));
    }
    return logic.mkAnd(std::move(cases));
}

PTRef IteToSwitch::conjoin(PTRef root) {
    return switches.size() == 0 ? root : logic.mkAnd(root, logic.mkAnd(switches));
};
