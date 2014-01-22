#include "simplifiers/TopLevelPropagate.h"
#include "common/TreeOps.h"

cgId SEnode::cgid_ctr = cgId_Nil+1;
SERef SEnode::SERef_Nil;

SEnode::SEnode(SymRef tr_, SERef er_) : symb(tr_), er(er_) {
    header.type = et_symb;
    cid = cgid_ctr++;
}

SEnode::SEnode(SERef car_, SERef cdr_,
             en_type t, SEAllocator& ea,
             SERef er_)
     : er(er_)
{
    header.type    = t;
    car            = car_;
    cdr            = cdr_;

    SEnode& x = ea[car];
    SEnode& y = ea[cdr];

    // What if x is symbol
    // What if y is nil
    SCgData& x_cgd = *x.cgdata;
    SCgData& y_cgd = *y.cgdata;

    SCgData& cgd   = *cgdata;

    cgd.root   = er;
    cgd.next   = er;
    cgd.size   = 1;
    cgd.parent = SERef_Undef;
    cgd.parent_size = 0;
    cid    = cgid_ctr++;

    if (x.type() != SEnode::et_symb) {
        // x is not a symbol
        if (x_cgd.parent == SERef_Undef) {
            x_cgd.parent  = er;
            cgd.same_car  = er;
        }
        else {
            cgd.same_car = ea[x_cgd.parent].cgdata->same_car;
            ea[x_cgd.parent].cgdata->same_car = er;
        }
        x_cgd.parent_size++;
    }
    else // x is a symbol
        cgd.same_car = er;

    if (y.type() != SEnode::et_symb) {
        if (y.getParent() == SERef_Undef) {
            y.setParent(er);
            setSameCdr(er);
        }
        else {
            setSameCdr(ea[y.getParent()].getSameCdr());
            ea[y.getParent()].setSameCdr(er);
        }
        y_cgd.parent_size++;
    }
    else {
        assert(cdr == SEnode::SERef_Nil);
        cgd.same_cdr = er;
    }
    cgd.cg_ptr = er;
}


TopLevelPropagator::TopLevelPropagator(Logic& l, Cnfizer& c) :
    logic(l)
  , cnfizer(c)
  , ea(1024*1024, sigtab)
{
    n_true = ea.alloc(ea.alloc(logic.getSym_true()), SEnode::SERef_Nil, SEnode::et_term, logic.getTerm_true());
    n_false = ea.alloc(ea.alloc(logic.getSym_false()), SEnode::SERef_Nil, SEnode::et_term, logic.getTerm_false());

}

void TopLevelPropagator::merge(SERef xr, SERef yr)
{
    if (ea[xr].getSize() < ea[yr].getSize()) {
        SERef tr = xr;
        xr = yr;
        yr = tr;
    }
    SEnode& x = ea[xr];
    SEnode& y = ea[yr];

    SERef wr = x.getParentSize() < y.getParentSize() ? xr : yr;
    SEnode& w = ea[wr];

    SERef pr = w.getParent();
    SERef prstart = pr;
    const bool scdr = w.isList();

    // Remove outdated signatures
    while (true) {
        SEnode& p = ea[pr];
        if (pr == p.getCgPtr()) {
            cgId car_id = ea[ea[p.getCar()].getRoot()].getCid();
            cgId cdr_id = ea[ea[p.getCdr()].getRoot()].getCid();
            sigtab.remove(SigPair(car_id, cdr_id));
        }
        pr = scdr ? p.getSameCdr() : p.getSameCar();
        if (pr == prstart) break;
    }
    // Set new root for eq class of y
    SERef vr = yr;
    SERef vrstart = vr;
    while (true) {
        SEnode& v = ea[vr];
        v.setRoot(xr);
        vr = v.getNext();
        if (vr == vrstart) break;
    }

    SERef tr = x.getNext();
    x.setNext(y.getNext());
    y.setNext(tr);

    x.setSize(x.getSize() + y.getSize());

    // I think saving the old cid is not required as we don't backtrack
    if (x.getParentSize() < y.getParentSize()) {
        CgId t = x.getCid();
        x.setCid(y.getCid());
        y.setCid(t);
    }

    // Insert new signatures an propagate congruences (5.5)
    pr = w.getParent();
    prstart = pr;
    while (true) {
        SEnode& p = ea[pr];
        SigPair k(ea[ea[p.getCar()].getRoot()].getCid(),
                  ea[ea[p.getCdr()].getRoot()].getCid());
        if ((pr == p.getCgPtr()) && sigtab.contains(k)) {
            p.setCgPtr(sigtab[k]);
            pending.push(SERefPair(pr, sigtab[k]));
        }else if (pr == p.getCgPtr()) {
            sigtab.insert(k, pr);
        }
        pr = scdr ? p.getSameCdr() : p.getSameCar();
        if (pr == prstart) break;
    }

    // Merge parent lists (6)
    if (y.getParent() != SERef_Undef) {
        if (x.getParent() == SERef_Undef)
            x.setParent(y.getParent());
        else if (x.isList()) {
            SERef tr = ea[x.getParent()].getSameCdr();
            SERef parent_samecdr_join = ea[y.getParent()].getSameCdr();
            ea[x.getParent()].setSameCdr(parent_samecdr_join);
            ea[y.getParent()].setSameCdr(tr);
        }
        else {
            SERef tr = ea[x.getParent()].getSameCar();
            ea[x.getParent()].setSameCar(ea[y.getParent()].getSameCar());
            ea[y.getParent()].setSameCar(tr);
        }
#ifdef PEDANTIC_DEBUG
        ea.checkEnodeAsrts(y.getParent());
#endif
    }
    x.setParentSize(x.getParentSize() + y.getParentSize());

}

bool TopLevelPropagator::assertEq(PTRef eqr)
{
    Pterm& eq = logic.getPterm(eqr);
    SERef eq_base = termToSERef[eq[0]];
    for (int i = 1; i < eq.size(); i++)
        pending.push(SERefPair(eq_base, termToSERef[eq[i]]));

    bool ok = true;
    while (pending.size() != 0 && ok) {
        SERef x = ea[pending.last().x].getRoot();
        SERef y = ea[pending.last().y].getRoot();
        pending.pop();
        if ((x == n_false && y == n_true) ||
            (y == n_false && x == n_true)) ok = false;
        else if (x != y) merge(x, y);
    }
    return ok;
}

//void TopLevelPropagator::merge(TopLevelPropagator::Node* x,
//                               TopLevelPropagator::Node* y)
//{
//    x = find(x);
//    y = find(y);
//
//    // Make sure the root is a var, if equality class contains a var
//    if (logic.isVar(x->tr)) y->parent = x;
//    else x->parent = y; }

//
// Extract the (more or less) cnfized structure starting from root,
// and update the list of substitutions based on top-level facts
// (equalities in the top-level conjunction of the cnf form)
//
bool TopLevelPropagator::updateBindings(PTRef root)
{

    // Insert terms to the enode structure
    vec<PtChild> terms;
    getTermList<PtChild>(root, terms, logic);
    for (int i = terms.size()-1; i >= 0; i--) {
        PtChild& ptc = terms[i];
        if (!termToSERef.contains(ptc.tr)) {
            // New term
            Pterm& t = logic.getPterm(ptc.tr);
            // 1. Find/define the symbol
            SymRef sr = t.symb();
            SERef ser;
            if (symToSERef.contains(sr))
                ser = symToSERef[sr];
            else {
                ser = ea.alloc(sr);
                symToSERef.insert(sr, ser);
            }
            // Construct the list enode
            SERef cdr = SEnode::SERef_Nil;
            for (int j = t.size()-1; j >= 0; j--) {
                SERef cdr_out;
                SERef car = termToSERef[t[j]];
                SigPair k(ea[ea[car].getRoot()].getCid(),
                          ea[ea[cdr].getRoot()].getCid());
                if (!sigtab.contains(k)) {
                    cdr_out = ea.alloc(car, cdr, SEnode::et_list, PTRef_Undef);
                    cdr = cdr_out;
                }
                else
                    cdr = sigtab[k];
            }
            SERef set = ea.alloc(ser, cdr, SEnode::et_term, ptc.tr);
            termToSERef.insert(ptc.tr, set);
#ifdef PEDANTIC_DEBUG
            cerr << logic.printTerm(ptc.tr) << " maps to "
                 << logic.printTerm(find(ptc.tr)) << endl;
#endif
        }
    }
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
//
//        // Join to true
//        if (logic.isUP(tr) && !logic.isEquality(tr) && !logic.isDisequality(tr) && sgn == l_True) {
//            if (PTRefToNode.contains(tr)) {
//                Node* n = find(PTRefToNode[tr]);
//                if (n->tr == logic.getTerm_false()) break;
//                else merge(n, &n_true); }
//            else {
//                Node* n = new Node(tr);
//                PTRefToNode.insert(tr, n);
//                merge(n, &n_true); }
//#ifdef PEDANTIC_DEBUG
//                cerr << logic.printTerm(tr) << " is an UP and will be substituted by "
//                     << logic.printTerm(logic.getTerm_true()) << endl;
//#endif
//        }
//
//        // Join to false
//        else if (logic.isUP(tr) && !logic.isEquality(tr) && sgn == l_False) {
//            if (PTRefToNode.contains(tr)) {
//                Node* n = find(PTRefToNode[tr]);
//                if (n->tr == logic.getTerm_true()) break;
//                else merge(n, &n_false);
//            }
//            else {
//                Node* n = new Node(tr);
//                PTRefToNode.insert(tr, n);
//                merge(n, &n_false);
//            }
//#ifdef PEDANTIC_DEBUG
//                cerr << logic.printTerm(tr) << " is an UP and will be substituted by "
//                     << logic.printTerm(logic.getTerm_false()) << endl;
//#endif
//        }
//
        // Join equalities
        if (logic.isEquality(tr) && sgn == l_True) {
#ifdef PEDANTIC_DEBUG
            cerr << "Identified an equality: " << logic.printTerm(tr) << endl;
#endif
            Pterm& t = logic.getPterm(tr);
            // n will be the reference
            if (!assertEq(tr)) break;

#ifdef PEDANTIC_DEBUG
            cerr << logic.printTerm(tr) << " is an equality and therefore the following replacements are in place:" << endl;
            for (int j = 0; j < t.size(); j++)
                cerr << "  [" << j << "] " << logic.printTerm(t[j]) << " replaced by "
                     << logic.printTerm(find(t[0]))  << endl;
#endif
        }
    }
    if (i < facts.size())
        return false;
    return true;
}

bool TopLevelPropagator::substitute(PTRef& root)
{
    int n_substs = 0;
    vec<PtChild> nodes;
    nodes.push(PtChild(root, PTRef_Undef, -1));


    while (nodes.size() > 0) {
        PtChild ctr = nodes.last(); nodes.pop();
        if (termToSERef.contains(ctr.tr)) {
            PTRef nr = find(ctr.tr);
            // p is the substituent nr
            if (nr != ctr.tr && logic.isVar(nr) && !contains(ctr.tr, nr)) {
#ifdef PEDANTIC_DEBUG
                cerr << "Will substitute " << logic.printTerm(ctr.tr)
                     << " with " << logic.printTerm(nr) << " in ";
#endif
                // Do the substitution
                if (ctr.parent == PTRef_Undef) {
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(root);
#endif
                    root = nr;
                }else{
                    Pterm& parent = logic.getPterm(ctr.parent);
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(ctr.parent) << ": ";
#endif
                    assert(parent.size() > ctr.pos);
                    parent[ctr.pos] = nr;
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(ctr.parent) << endl;
#endif
                }
                n_substs++;
                continue;
            }
        }
        Pterm& t = logic.getPterm(ctr.tr);
        for (int i = 0; i < t.size(); i++)
            nodes.push(PtChild(t[i], ctr.tr, i));
    }
    return n_substs > 0;

}

// This is not yet implemented
bool TopLevelPropagator::contains(PTRef x, PTRef y) { return false; }


