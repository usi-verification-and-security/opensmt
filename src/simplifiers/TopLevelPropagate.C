/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/


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
  , total_substs(0)
{
    n_true = ea.alloc(ea.alloc(logic.getSym_true()), SEnode::SERef_Nil, SEnode::et_term, logic.getTerm_true());
    n_false = ea.alloc(ea.alloc(logic.getSym_false()), SEnode::SERef_Nil, SEnode::et_term, logic.getTerm_false());

}

//
// The merge function.  We make an attempt that the canonical representative
// would not be contained in any term in the equivalence class, but
// guarantee nothing.
//
void TopLevelPropagator::merge(SERef xr, SERef yr)
{
    if ((ea[xr] < ea[yr]) && (!ea[yr].isTerm() || !contains(ea[yr].getTerm(), ea[xr].getTerm()))) {
        SERef tr = xr;
        xr = yr;
        yr = tr;
    }
    SEnode& x = ea[xr];
    SEnode& y = ea[yr];
    if (x.type() == SEnode::et_term) {
#ifdef PEDANTIC_DEBUG
        cerr << "Merging terms " << logic.printTerm(x.getTerm())
             << " and " << logic.printTerm(y.getTerm())
             << ".  The root will be "
             << logic.printTerm(x.getTerm()) << endl;
#endif
    }
    SERef wr = x.getParentSize() < y.getParentSize()  ? xr : yr;
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


//
// The substitutions for the term riddance from osmt1
//
#ifdef SIMPLIFY_DEBUG
void TopLevelPropagator::retrieveSubstitutions(PTRef root, Map<PTRef,PTRef,PTRefHash>& substs, Map<PTRef,int,PTRefHash>& subst_targets, vec<PTRef>& subst_vars)
#else
void TopLevelPropagator::retrieveSubstitutions(PTRef root, Map<PTRef,PTRef,PTRefHash>& substs, Map<PTRef,int,PTRefHash>& subst_targets)
#endif
{
    vec<PtAsgn> facts;

    collectFacts(root, facts);

    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        // Join equalities
        if (logic.isEquality(tr) && sgn == l_True) {
#ifdef SIMPLIFY_DEBUG
            cerr << "Identified an equality: " << logic.printTerm(tr) << endl;
#endif
            Pterm& t = logic.getPterm(tr);
            // n will be the reference
//            if (!assertEq(tr)) break;
            // This is the simple replacement to elimiate enode terms where possible
            assert(t.size() == 2);
            // One of them should be a var
            Pterm& a1 = logic.getPterm(t[0]);
            Pterm& a2 = logic.getPterm(t[1]);
            if (a1.size() == 0 || a2.size() == 0) {
                PTRef var = a1.size() == 0 ? t[0] : t[1];
                PTRef trm = a1.size() == 0 ? t[1] : t[0];
                if (contains(trm, var)) continue;
#ifdef SIMPLIFY_DEBUG
                if (substs.contains(var)) {
                    cerr << "Double substitution:" << endl;
                    cerr << " " << logic.printTerm(var) << "/" << logic.printTerm(trm) << endl;
                    cerr << " " << logic.printTerm(var) << "/" << logic.printTerm(substs[var]) << endl;
                } else {
                    subst_vars.push(var);
                    char* tmp1 = logic.printTerm(var);
                    char* tmp2 = logic.printTerm(trm);
                    cerr << "Substituting " << tmp1 << " with " << tmp2 << endl;
                    ::free(tmp1); ::free(tmp2);
                }
#endif
                if (!substs.contains(var)) {
                    substs.insert(var, trm);
                    if (!subst_targets.contains(trm))
                        subst_targets.insert(trm, 1);
                    else
                        subst_targets[trm]++;
#ifdef SIMPLIFY_DEBUG
                    cerr << "Subst target (" << subst_targets[trm] << " fold): " << logic.printTerm(trm) << endl;
#endif
                } else {
                    assert(subst_targets.contains(substs[var]));
                    subst_targets[substs[var]]--;
                    if (subst_targets[substs[var]] == 0)
                        subst_targets.remove(substs[var]);
                    substs.remove(var);
                    if (subst_targets.contains(trm))
                        subst_targets[trm]++;
                    else
                        subst_targets.insert(trm, 1);
                    substs.insert(var,trm);
                }
            }
        }
    }
}

void TopLevelPropagator::collectFacts(PTRef root, vec<PtAsgn>& facts)
{
    Map<PTRef,bool,PTRefHash> isdup;
    vec<PtAsgn> queue;
    PTRef p;
    lbool sign;
    cnfizer.purify(root, p, sign);
    queue.push(PtAsgn(p, sign));

    while (queue.size() != 0) {
        PtAsgn pta = queue.last(); queue.pop();

        if (isdup.contains(pta.tr)) continue;
        isdup.insert(pta.tr, true);

        Pterm& t = logic.getPterm(pta.tr);

        if (logic.isAnd(pta.tr) and pta.sgn == l_True)
            for (int i = 0; i < t.size(); i++) {
                PTRef c;
                lbool c_sign;
                cnfizer.purify(t[i], c, c_sign);
                queue.push(PtAsgn(c, pta.sgn == l_True ? c_sign : c_sign^true));
            }
        else if (logic.isOr(pta.tr) and (pta.sgn == l_False))
            for (int i = 0; i < t.size(); i++) {
                PTRef c;
                lbool c_sign;
                cnfizer.purify(t[i], c, c_sign);
                queue.push(PtAsgn(c, c_sign^true));
            }
        // unary and negated
        else if (logic.isAnd(pta.tr) and (pta.sgn == l_False) and (t.size() == 1)) {
            PTRef c;
            lbool c_sign;
            cnfizer.purify(t[0], c, c_sign);
            queue.push(PtAsgn(c, c_sign^true));
        }
        // unary or
        else if (logic.isOr(pta.tr) and (pta.sgn == l_True) and (t.size() == 1)) {
            PTRef c;
            lbool c_sign;
            cnfizer.purify(t[0], c, c_sign);
            queue.push(PtAsgn(c, c_sign));
        }
        // Found a fact.  It is important for soundness that we have also the original facts
        // asserted to the euf solver in the future even though no search will be performed there.
        else if (logic.isEquality(pta.tr) and pta.sgn == l_True) {
            facts.push(pta);
        }
        else if (logic.isUP(pta.tr)) {
            facts.push(pta);
        }
    }

#ifdef SIMPLIFICATION_DEBUG
    cerr << "True facts" << endl;
    for (int i = 0; i < facts.size(); i++)
        cerr << (facts[i].sgn == l_True ? "" : "not ") << logic.printTerm(facts[i].tr) << " (" << facts[i].tr.x << ")" << endl;
#endif
}


//
// Initialize the small congruence data structure with the relevant nodes starting from root
//
void TopLevelPropagator::initCongruence(PTRef root)
{
    // Insert terms to the enode structure
    vec<PtChild> terms;
    getTermList<PtChild>(root, terms, logic);
    for (int i = 0; i < terms.size(); i++) {
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
        }
    }
}


//
// The congruence substitution scheme.  This seems to have some potential based
// on both earlier experimentation and pen and paper.
//
bool TopLevelPropagator::computeCongruenceSubstitutions(PTRef root, vec<PtAsgn>& facts)
{
    collectFacts(root, facts);
    int i;
    for (i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;

        // Join to true
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

        // Join equalities
//        else if (logic.isEquality(tr) && sgn == l_True)
        if (logic.isEquality(tr) && sgn == l_True) {
#ifdef PEDANTIC_DEBUG
            cerr << "Identified an equality: " << logic.printTerm(tr) << endl;
#endif
            Pterm& t = logic.getPterm(tr);
            // n will be the reference
            if (!assertEq(tr)) break;
            // This is the simple replacement to elimiate enode terms where possible
            assert(t.size() == 2);
#ifdef PEDANTIC_DEBUG
            cerr << logic.printTerm(tr) << " is an equality and therefore the following replacements are in place:" << endl;
            for (int j = 0; j < t.size(); j++)
                cerr << "  [" << j << "] " << logic.printTerm(t[j])
                     << " (" << t[j].x << ") replaced by "
                     << logic.printTerm(find(t[0])) << " (" << find(t[0]).x << ")" << endl;
#endif
        }
    }

    if (i < facts.size())
        return false;
    return true;

}


//
// Extract the (more or less) cnfized structure starting from root,
// and update the list of substitutions based on top-level facts
// (equalities in the top-level conjunction of the cnf form)
//
// We have two types of information here.  One is to compute equivalence
// classes on top level and use the information to prune down the number of
// equivalences we see during the search.  The other is to try to substitute
// enode variables with terms not containing the variables to reduce the number
// of enode variables we need to handle.  It seems that at least the use of
// only the former does not result in as good a speed-up as the use of only the
// latter.  It would be interesting to test whether combining the two would be
// useful in theory and practice.
//
//bool TopLevelPropagator::updateBindings(PTRef root, vec<PTRef>& tlfacts, Map<PTRef,PTRef,PTRefHash>& substs)
//{
//    // Find equalities that are true/false on the abstract top (Boolean)
//    // level
//    int i;
//
//    vec<PTRef> facts;
//    collectFacts(root, facts, tlfacts);
//
//    for (i = 0; i < facts.size(); i++) {
//        PTRef tr = facts[i].tr;
//        lbool sgn = facts[i].sgn;
//        // Join equalities
//        if (logic.isEquality(tr) && sgn == l_True) {
//#ifdef PEDANTIC_DEBUG
//            cerr << "Identified an equality: " << logic.printTerm(tr) << endl;
//#endif
//            Pterm& t = logic.getPterm(tr);
//            // n will be the reference
////            if (!assertEq(tr)) break;
//            // This is the simple replacement to elimiate enode terms where possible
//            assert(t.size() == 2);
//            // One of them should be a var
//            Pterm& a1 = logic.getPterm(t[0]);
//            Pterm& a2 = logic.getPterm(t[1]);
//            if (a1.size() == 0 || a2.size() == 0) {
//                PTRef var = a1.size() == 0 ? t[0] : t[1];
//                PTRef trm = a1.size() == 0 ? t[1] : t[0];
//                if (contains(trm, var)) continue;
//#ifdef PEDANTIC_DEBUG
//                if (substs.contains(var)) {
//                    cerr << "Double substitution:" << endl;
//                    cerr << " " << logic.printTerm(var) << "/" << logic.printTerm(trm) << endl;
//                    cerr << " " << logic.printTerm(var) << "/" << logic.printTerm(substs[var]) << endl;
//                }
//#endif
//                substs.insert(var, logic.cloneTerm(trm));
//            }
//
//#ifdef PEDANTIC_DEBUG
////            cerr << logic.printTerm(tr) << " is an equality and therefore the following replacements are in place:" << endl;
////            for (int j = 0; j < t.size(); j++)
////                cerr << "  [" << j << "] " << logic.printTerm(t[j]) << " replaced by "
////                     << logic.printTerm(find(t[0]))  << endl;
//#endif
//        }
//    }
//    if (i < facts.size())
//        return false;
//    return true;
//}

#ifdef OSMT1_SUBSTITUTION
//
// Compute the generalized substitution based on substs, and return in
// tr_new the corresponding term dag.
// Preconditions:
//  - all substitutions in substs must be on variables
//
bool TopLevelPropagator::varsubstitute(PTRef& root, Map<PTRef,PTRef,PTRefHash>& substs, Map<PTRef,int,PTRefHash>& subst_targets, PTRef& tr_new)
{
    Map<PTRef,PTRef,PTRefHash> gen_sub;
    vec<PTRef> queue;
    int n_substs = 0;

    queue.push(root);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (gen_sub.contains(tr)) {
            // Already processed
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            if (!gen_sub.contains(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true;
            }
        }
        if (unprocessed_children) continue;
        queue.pop();
        PTRef result = PTRef_Undef;
        if (logic.isVar(tr) || logic.isConst(tr)) {
            // The base case
            if (substs.contains(tr))
                result = substs[tr];
            else
                result = tr;
            assert(!logic.isConst(tr) || result == tr);
        } else {
            // The "inductive" case
            vec<PTRef> args_mapped;
            for (int i = 0; i < t.size(); i++)
                args_mapped.push(gen_sub[t[i]]);
            const char* msg;
            result = logic.insertTerm(t.symb(), args_mapped, &msg);

        }
        gen_sub.insert(tr, result);
        assert(result != PTRef_Undef);

        if (result != tr) {
            n_substs++;
#ifdef SIMPLIFY_DEBUG
            cerr << "Will substitute " << logic.printTerm(tr) << " with " << logic.printTerm(result) << endl;
#endif
        }
    }
    tr_new = gen_sub[root];
    return n_substs > 0;
}
#else

//
// Substitution aiming at minimizing the number of enode variables.
// Depth-first search through the tree starting at root.
//
//  - Stop expansion when a substitution is done.  Otherwise inifinte substitution chains are
//    possible
//  - Always use logic.insertTerm() to avoid constructing
//    duplicate terms!
//
#ifndef OLD_VARSUBSTITUTE
bool TopLevelPropagator::varsubstitute(PTRef& root, Map<PTRef,PTRef,PTRefHash>& substs, Map<PTRef,int,PTRefHash>& subst_targets, PTRef& tr_new)
#else
bool TopLevelPropagator::varsubstitute(PTRef& root, Map<PTRef,PTRef,PTRefHash>& substs)
#endif
{
#ifndef OLD_VARSUBSTITUTE
    Map<PTRef, PTRef, PTRefHash> subst;

    vec<pi> queue;
    Map<PTRef,bool,PTRefHash> processed;

    queue.push(pi(root));
    int n_substs = 0;

    while (queue.size() > 0) {
        int idx = queue.size() - 1;
        Pterm& t = logic.getPterm(queue[idx].x);
        if (processed.contains(queue[idx].x)) {
            queue.pop();
            continue;
        }
        if (!queue[idx].done) {
            for (int i = 0; i < t.size(); i++) {
                if (subst_targets.contains(t[i])) {
                    subst.insert(t[i], t[i]);
                    continue;
                }
                PTRef c_n = t[i];
                if (substs.contains(t[i])) {
                    c_n = substs[t[i]];
                    if (contains(c_n, t[i]))
                        continue;

                }
                if (c_n == t[i]) {
                    queue.push(pi(t[i]));
                } else {
                    n_substs++;
                    subst.insert(t[i], c_n);
                }
            }
            queue[idx].done = true;
            continue;
        }

        // We are coming back now
        vec<PTRef> args;
        for (int i = 0; i < t.size(); i++)
            args.push(subst[t[i]]);

        const char** msg = NULL;
        PTRef tr_n = logic.insertTerm(t.symb(), args, msg);

        assert(!subst.contains(queue[idx].x));
        subst.insert(queue[idx].x, tr_n);
        processed.insert(queue[idx].x, true);
        queue.pop();
    }

    assert(subst.contains(root));
    tr_new = subst[root];
    total_substs += n_substs;

    return n_substs > 0;

#else
    int n_substs = 0;
    vec<PTRef> nodes;

    nodes.push(root);
    while (nodes.size() > 0) {
        PTRef tr = nodes.last();
        nodes.pop();
        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            if (substs.contains(t[i])) {
                PTRef nr = substs[t[i]];
                if (contains(nr, t[i])) {
                    continue;
                }
#ifdef PEDANTIC_DEBUG
                cerr << "Will substitute " << logic.printTerm(t[i])
                     << " with " << logic.printTerm(nr) << " in "
                     << logic.printTerm(tr);
#endif
                t[i] = substs[t[i]];
#ifdef PEDANTIC_DEBUG
                cerr << ": " << logic.printTerm(tr) << "(" << tr.x << ")" << endl;
#endif
                n_substs++;
            }
            nodes.push(t[i]);
        }
    }
    total_substs += n_substs;
    return n_substs > 0;
#endif
}
#endif // OSMT1_SUBSTITUTION

// --------------------------------------------------------------
// TopLevelPropagator::substitute
//
// The substitution based on equivalence classes computed with
// congruence closure.
//
// Starting from the root go depth-first, pre-order through the term
// dag.  Stop expansion of a path starting from a child if the child has
// been processed before or if there is a substitution for the child.
// Produce a new term tree (reusing the old terms where possible).
//


bool TopLevelPropagator::substitute(PTRef& root, PTRef& tr_new)
{
    Map<PTRef, PTRef, PTRefHash> subst;

    vec<pi> queue;
    Map<PTRef,bool,PTRefHash> processed;

    queue.push(pi(root));
    int n_substs = 0;

    while (queue.size() > 0) {
        int idx = queue.size() - 1;
        Pterm& t = logic.getPterm(queue[idx].x);
        if (processed.contains(queue[idx].x)) {
            queue.pop();
            continue;
        }
        if (!queue[idx].done) {
            for (int i = 0; i < t.size(); i++) {
                PTRef c_n = find(t[i]);
                c_n == t[i] ? queue.push(pi(t[i])) : (n_substs++, subst.insert(t[i], c_n));
            }
            queue[idx].done = true;
            continue;
        }

        // We are coming back now
        vec<PTRef> args;
        for (int i = 0; i < t.size(); i++)
            args.push(subst[t[i]]);

        const char** msg;
        PTRef tr_n = logic.insertTerm(t.symb(), args, msg);

        assert(!subst.contains(queue[idx].x));
        subst.insert(queue[idx].x, tr_n);
        processed.insert(queue[idx].x, true);
        queue.pop();
    }

    assert(subst.contains(root));
    tr_new = subst[root];

    return n_substs > 0;
}


//
// Does term contain var?  (works even if var is a term...)
//
bool TopLevelPropagator::contains(PTRef term, PTRef var)
{
    Map<PTRef, bool, PTRefHash> proc;
    vec<PTRef> queue;
    queue.push(term);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (tr == var) return true;
        if (proc.contains(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++)
            if (!proc.contains(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true; }
        if (unprocessed_children) continue;
        queue.pop();
        proc.insert(tr, true);
    }
    return false;
}

PTRef TopLevelPropagator::learnEqTransitivity(PTRef formula)
{
    vec<PTRef> implications;
    vec<PTRef> queue;
    Map<PTRef,bool,PTRefHash> processed;

    queue.push(formula);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (processed.contains(tr)) {
            queue.pop(); continue; }

        Pterm& t = logic.getPterm(tr);
        bool unp_ch = false;
        for (int i = 0; i < t.size(); i++) {
            if (!processed.contains(t[i])) {
                queue.push(t[i]);
                unp_ch = true;
            }
        }
        if (unp_ch) continue;

        queue.pop();
        //
        // Add (or (and (= x w) (= w z)) (and (= x y) (= y z))) -> (= x z)
        //

        const bool cond1 = logic.isOr(tr) && t.size() == 2 &&
                           logic.isAnd(t[0]) && logic.isAnd(t[1]) &&
                           logic.isEquality(logic.getPterm(t[0])[0]) &&
                           logic.isEquality(logic.getPterm(t[0])[1]) &&
                           logic.isEquality(logic.getPterm(t[1])[0]) &&
                           logic.isEquality(logic.getPterm(t[1])[1]);

        if (cond1) {
            // (= v1 v2) (= v3 v4)
            PTRef v1 = logic.getPterm(logic.getPterm(t[0])[0])[0];
            PTRef v2 = logic.getPterm(logic.getPterm(t[0])[0])[1];
            PTRef v3 = logic.getPterm(logic.getPterm(t[0])[1])[0];
            PTRef v4 = logic.getPterm(logic.getPterm(t[0])[1])[1];

            // (= t1 t2) (= t3 t4)
            PTRef t1 = logic.getPterm(logic.getPterm(t[1])[0])[0];
            PTRef t2 = logic.getPterm(logic.getPterm(t[1])[0])[1];
            PTRef t3 = logic.getPterm(logic.getPterm(t[1])[1])[0];
            PTRef t4 = logic.getPterm(logic.getPterm(t[1])[1])[1];

            // Detecting bridging variables
            const bool cond2a = v1 == v3 || v1 == v4 || v2 == v3 || v2 == v4;
            const bool cond2b = t1 == t3 || t1 == t4 || t2 == t3 || t2 == t4;

            if (cond2a && cond2b) {
                PTRef w  = (v1 == v3 || v1 == v4 ? v1 : v2);
                PTRef x1 = (v1 == w ? v2 : v1);
                PTRef z1 = (v3 == w ? v4 : v3);

                PTRef y  = (t1 == t3 || t1 == t4 ? t1 : t2);
                PTRef x2 = (t1 == y ? t2 : t1);
                PTRef z2 = (t3 == y ? t4 : t3);

                const bool cond2 = (x1 == x2 && z1 == z2) || (x1 == z2 && x2 == z1);
                if (cond2) {
                    vec<PTRef> args_eq;
                    args_eq.push(x1);
                    args_eq.push(z1);
                    PTRef eq = logic.mkEq(args_eq);
                    vec<PTRef> args_impl;
                    args_impl.push(tr);
                    args_impl.push(eq);
                    PTRef impl = logic.mkImpl(args_impl);
                    implications.push(impl);
                }
            }
        }
        processed.insert(tr, true);
    }

    if (implications.size() > 0)
        return logic.mkAnd(implications);
    else
        return PTRef_Undef;
}
