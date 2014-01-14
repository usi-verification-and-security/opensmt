#include "simplifiers/TopLevelPropagate.h"

TopLevelPropagator::TopLevelPropagator(Logic& l, Cnfizer& c) :
    logic(l)
  , cnfizer(c)
  , n_false(logic.getTerm_false())
  , n_true(logic.getTerm_true())
{
    PTRefToNode.insert(logic.getTerm_false(), &n_false);
    PTRefToNode.insert(logic.getTerm_true(), &n_true);
}

TopLevelPropagator::Node* TopLevelPropagator::find(TopLevelPropagator::Node* n)
{
    if (n != n->parent)
        n->parent = find(n->parent);
    return n->parent; }

void TopLevelPropagator::merge(TopLevelPropagator::Node* x,
                               TopLevelPropagator::Node* y)
{
    x = find(x);
    y = find(y);

    // Make sure the root is a var, if equality class contains a var
    if (logic.isVar(x->tr)) y->parent = x;
    else x->parent = y; }

bool TopLevelPropagator::insertBindings(PTRef root)
{
    // Find equalities that are true/false on the abstract top (Boolean)
    // level
    vec<PtAsgn> facts;
    vec<PTRef> queue;
    PTRef purified;
    lbool sign;
    cnfizer.purify(root, purified, sign);
    queue.push(purified);

    while (queue.size() != 0) {
        PTRef pt_r = queue.last(); queue.pop();
        cnfizer.purify(pt_r, purified, sign);
        Pterm& pt = logic.getPterm(purified);
        if (logic.isAnd(purified) and sign == l_True)
            for (int i = 0; i < pt.size(); i++)
                queue.push(pt[i]);

        else if (logic.isOr(purified) and sign == l_False)
            for (int i = 0; i < pt.size(); i++)
                queue.push(pt[i]);

        else if (logic.isEquality(purified) || logic.isUP(purified))
            facts.push(PtAsgn(purified, sign));
        // Missing: unary ors and ands
    }

#ifdef PEDANTIC_DEBUG
    cerr << "True facts" << endl;
    for (int i = 0; i < facts.size(); i++)
        cerr << (facts[i].sgn == l_True ? "" : "not ") << logic.printTerm(facts[i].tr) << endl;
#endif

    int i;

    for (i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;

        // Join to true
        if (logic.isUP(tr) && !logic.isEquality(tr) && sgn == l_True) {
            if (PTRefToNode.contains(tr)) {
                Node* n = find(PTRefToNode[tr]);
                if (n->tr == logic.getTerm_false()) break;
                else merge(n, &n_true); }
            else {
                Node* n = new Node(tr);
                PTRefToNode.insert(tr, n);
                merge(n, &n_true); }
#ifdef PEDANTIC_DEBUG
                cerr << logic.printTerm(tr) << " is an UP and will be substituted by "
                     << logic.printTerm(logic.getTerm_true()) << endl;
#endif
        }

        // Join to false
        else if (logic.isUP(tr) && !logic.isEquality(tr) && sgn == l_False) {
            if (PTRefToNode.contains(tr)) {
                Node* n = find(PTRefToNode[tr]);
                if (n->tr == logic.getTerm_true()) break;
                else merge(n, &n_false);
            }
            else {
                Node* n = new Node(tr);
                PTRefToNode.insert(tr, n);
                merge(n, &n_false);
            }
#ifdef PEDANTIC_DEBUG
                cerr << logic.printTerm(tr) << " is an UP and will be substituted by "
                     << logic.printTerm(logic.getTerm_false()) << endl;
#endif
        }

        // Join equalities
        else if (logic.isEquality(tr) && sgn == l_True) {
            Pterm& t = logic.getPterm(tr);
            Node * n;
            // n will be the reference
            if (PTRefToNode.contains(t[0]))
                n = PTRefToNode[t[0]];
            else {
                n = new Node(t[0]);
                PTRefToNode.insert(t[0], n);
            }

            for (int j = 1; j < t.size(); j++) {
                Node* m;
                if (PTRefToNode.contains(t[j]))
                    m = PTRefToNode[t[j]];
                else {
                    m = new Node(t[j]);
                    PTRefToNode.insert(tr, m);
                }
                merge(n, m);
            }
#ifdef PEDANTIC_DEBUG
            cerr << logic.printTerm(tr) << " is an equality and therefore its arguments ";
            for (int j = 0; j < t.size(); j++)
                cerr << logic.printTerm(t[j]) << " ";
            cerr << " are currently all replaced by "
                 << logic.printTerm(find(n)->tr)  << endl;
#endif
        }
    }
    if (i < facts.size())
        return false;
    return true;
}

void TopLevelPropagator::substitute(PTRef& root)
{
    vec<PtChild> nodes;
    nodes.push(PtChild(root, PTRef_Undef, -1));

    while (nodes.size() > 0) {
        PtChild& ctr = nodes.last(); nodes.pop();
        if (PTRefToNode.contains(ctr.tr)) {
            Node* n = PTRefToNode[ctr.tr];
            Node* p = find(n);
            if (n != p && logic.isVar(p->tr) && !contains(n->tr, p->tr)) {
#ifdef PEDANTIC_DEBUG
                cerr << "Will substitute " << logic.printTerm(n->tr)
                     << " with " << logic.printTerm(p->tr) << " in ";
#endif
                // Do the substitution
                if (ctr.parent == PTRef_Undef) {
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(root);
#endif
                    root = p->tr;
                }else{
                    Pterm& parent = logic.getPterm(ctr.parent);
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(ctr.parent) << ": ";
#endif
                    parent[ctr.pos] = p->tr;
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(ctr.parent) << endl;
#endif
                }
                continue;
            }
        }
        Pterm& t = logic.getPterm(ctr.tr);
        for (int i = 0; i < t.size(); i++)
            nodes.push(PtChild(t[i], ctr.tr, i));
    }

}

// This is not yet implemented
bool TopLevelPropagator::contains(PTRef x, PTRef y) { return false; }
