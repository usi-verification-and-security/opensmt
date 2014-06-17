#include "MainSolver.h"
#include "TreeOps.h"

sstat MainSolver::simplifyFormulas(char** err_msg) {
    sstat  state = s_Undef;
    PTRef  root;
    // Think of something here to enable incrementality...
    if (!ts.solverEmpty()) {
        asprintf(err_msg, "Solver already contains a simplified problem.  Cannot continue for now");
        return s_Error; }

    // XXX Disable this once debugging phase is over
    vec<PTRef> tmp;
    for (int i = formulas.size()-1; i >= 0; i--)
        tmp.push(formulas[i]);
    root = logic.mkAnd(tmp);
//    root = logic.mkAnd(formulas);
    PTRef trans = PTRef_Undef;
    trans = tlp.learnEqTransitivity(root);
    if (trans != PTRef_Undef) {
        vec<PTRef> enriched;
        enriched.push(trans);
        enriched.push(root);
        root = logic.mkAnd(enriched);
    }
    // Framework for handling different logic related simplifications.
    // For soundness it is important to run this until closure
    Map<PTRef,PTRef,PTRefHash> substs;
    while (true) {
#ifdef PEDANTIC_DEBUG
        cerr << "retrieving" << endl;
        vec<PTRef> subst_vars;
        tlp.retrieveSubstitutions(root, substs, subst_vars);
        cerr << "Identified substitutions: " << endl;
        for (int i = 0; i < subst_vars.size(); i++)
            cerr << "Substituting " << logic.printTerm(subst_vars[i]) << " with " << logic.printTerm(substs[subst_vars[i]]) << endl;
#else
        tlp.retrieveSubstitutions(root, substs);
#endif

//        if (!tlp.substitute(root)) break;
#ifdef PEDANTIC_DEBUG
        cerr << "substituting" << endl;
#endif
        if (!tlp.varsubstitute(root, substs)) break;
        lbool res = logic.simplifyTree(root);
        if (res == l_True) root = logic.getTerm_true(); // Trivial problem
        else if (res == l_False) root = logic.getTerm_false(); // Trivial problem
    }

    vec<PtAsgn> tlfacts;
//#ifdef PEDANTIC_DEBUG
//    cerr << "Init congruence with " << logic.printTerm(root) << endl;
//#endif
//    tlp.initCongruence(root);
//
//#ifdef PEDANTIC_DEBUG
//    cerr << "Compute congruence substitution" << endl;
//#endif
//    if (!tlp.computeCongruenceSubstitutions(root, tlfacts)) {
//        root = logic.getTerm_false(); // trivial problem
//    }
//    PTRef new_root;
//    tlp.substitute(root, new_root);
//    root = new_root;

    {
        // Add the top level facts to the formula
        vec<PTRef> tmp;
        tmp.push(root);
        for (int i = 0; i < tlfacts.size(); i++)
            tmp.push(tlfacts[i].sgn == l_True ? tlfacts[i].tr : logic.mkNot(tlfacts[i].tr));
        root = logic.mkAnd(tmp);
        lbool res = logic.simplifyTree(root);
        if (res == l_True) root = logic.getTerm_true(); // Trivial problem
        else if (res == l_False) root = logic.getTerm_false(); // Trivial problem
        vec<PtChild> terms;
        FContainer fc(root);
        expandItes(fc, terms);
        fc.setRoot(terms[terms.size()-1].tr);
        // tmp debug
        PTRef root = fc.getRoot();
        Pterm& r = logic.getPterm(root);

        // XXX There should be no reason to do this one by one, and in fact it
        // should be harmful since the shared structure will be invisible that
        // way.
#ifdef OLD_SIMPLIFICATION
        vec<PTRef> tlfs;
        ts.retrieveTopLevelFormulae(root, tlfs);
        for (int i = 0; (i < tlfs.size()) && (state == s_Undef); i++) {
            if (ts.checkDeMorgan(tlfs[i]) || ts.checkCnf(tlfs[i]) || ts.checkClause(tlfs[i]))
                fc.setRoot(tlfs[i]);
            else {
                fc.setRoot(tlfs[i]);
                fc = propFlatten(fc);
            }
            terms.clear();
            getTermList(fc.getRoot(), terms, logic);
            fc = simplifyEqualities(terms);
            lbool res = logic.simplifyTree(fc.getRoot());
#ifdef SIMPLIFY_DEBUG
            cerr << "After simplification got " << endl;
            if (res == l_Undef)
                 cerr << logic.printTerm(fc.getRoot()) << endl;
            else if (res == l_False)
                cerr << logic.printTerm(logic.getTerm_false()) << endl;
            else if (res == l_True)
                cerr << logic.printTerm(logic.getTerm_true()) << endl;
            else
                assert(false);
#endif
            
            if (res == l_False) state = giveToSolver(logic.getTerm_false());
            else if (res == l_Undef)
                state = giveToSolver(fc.getRoot());
        }
#else
        fc = propFlatten(fc);
        terms.clear();
        getTermList(fc.getRoot(), terms, logic);
        fc = simplifyEqualities(terms);
        res = logic.simplifyTree(fc.getRoot());
        if (res == l_False) state = giveToSolver(logic.getTerm_false());
        else if (res == l_Undef)
            state = giveToSolver(fc.getRoot());
#endif

//        vec<PTRef> tlfs;
//        ts.retrieveTopLevelFormulae(root, tlfs);
//        for (int i = 0; (i < tlfs.size()) && (state == s_Undef); i++) {
//            if (ts.checkDeMorgan(tlfs[i]) || ts.checkCnf(tlfs[i]) || ts.checkClause(tlfs[i]))
//                fc.setRoot(tlfs[i]);
//            else {
//                fc.setRoot(tlfs[i]);
//                fc = propFlatten(fc);
//            }
//            terms.clear();
//            getTermList(fc.getRoot(), terms, logic);
//            fc = simplifyEqualities(terms);
//            lbool res = logic.simplifyTree(fc.getRoot());
//#ifdef SIMPLIFY_DEBUG
//            cerr << "After simplification got " << endl;
//            if (res == l_Undef)
//                 cerr << logic.printTerm(fc.getRoot()) << endl;
//            else if (res == l_False)
//                cerr << logic.printTerm(logic.getTerm_false()) << endl;
//            else if (res == l_True)
//                cerr << logic.printTerm(logic.getTerm_true()) << endl;
//            else
//                assert(false);
//#endif
//            if (res == l_False) state = giveToSolver(logic.getTerm_false());
//            else if (res == l_Undef)
//                state = giveToSolver(fc.getRoot());
//        }
    }
end:
    return state;
}

void MainSolver::expandItes(FContainer& fc, vec<PtChild>& terms) const
{
    // cnfization of the formula
    // Get the egraph data structure for instance from here
    // Terms need to be purified before cnfization?

    PTRef root = fc.getRoot();

    getTermList<PtChild>(root, terms, logic);

    if (terms.size() > 0) {
        root = ts.expandItes(terms);
        terms.clear();
        // This seems a bit subtle way of updating the terms vector
        getTermList<PtChild>(root, terms, logic);
    }
    fc.setRoot(root);
}


#ifdef ENABLE_SHARING_BUG
MainSolver::FContainer MainSolver::mergeEnodeArgs(PTRef fr, Map<PTRef, PTRef, PTRefHash>& cache, Map<PTRef, int, PTRefHash>& occs)
{
    assert(logic.isAnd(fr) || logic.isOr(fr));
    Pterm& f = logic.getPterm(fr);
    SymRef sr = f.symb();
    vec<PTRef> new_args;
#ifdef PEDANTIC_DEBUG
    char* name = logic.printTerm(fr);
    cout << "; Merge: " << name << endl;
    ::free(name);
#endif
    for (int i = 0; i < f.size(); i++) {
        PTRef arg = f[i];
        PTRef sub_arg = cache[arg];
        SymRef sym = logic.getPterm(arg).symb();
        if (sym != sr) {
            new_args.push(sub_arg);
            continue;
        }
        assert(occs.contains(arg));
        assert(occs[arg] >= 1);

        if (occs[arg] > 1) {
            new_args.push(sub_arg);
#ifdef PEDANTIC_DEBUG
            cout << " Using shared structure (" << occs[arg] << " * ";
            char* name = logic.printTerm(sub_arg);
            cout << name << endl;
            ::free(name);
#endif
            continue;
        }
        Pterm& sa = logic.getPterm(sub_arg);
        for (int j = 0; j < sa.size(); j++)
            new_args.push(sa[j]);
    }
    const char* msg;
    PTRef out = logic.mkFun(sr, new_args, &msg);
#ifdef PEDANTIC_DEBUG
    cout << " =>    ";
    name = logic.printTerm(out);
    cout << name << endl;
    ::free(name);
#endif
    return out;
}

MainSolver::FContainer MainSolver::rewriteMaxArity(MainSolver::FContainer fc, Map<PTRef, int, PTRefHash>& occs)
{
    PTRef f = fc.getRoot();
    vec<PTRef> queue;
    queue.push(f);
    Map<PTRef,PTRef,PTRefHash> cache; // Cache for processed nodes

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        Pterm& t = logic.getPterm(tr);
        if (cache.contains(tr)) {
            queue.pop();
            continue;
        }

        bool unprocessed_children = false;
        for (int i = 0; i < t.size(); i++) {
            if (logic.isBooleanOperator(t[i]) && !cache.contains(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true;
            } else if (logic.isAtom(t[i]))
                cache.insert(t[i], t[i]);
        }
        if (unprocessed_children) continue;
        queue.pop();
        assert(logic.isBooleanOperator(tr) || logic.isTrue(tr) || logic.isFalse(tr));
        PTRef result;
        if (logic.isAnd(tr) || logic.isOr(tr))
            result = mergeEnodeArgs(tr, cache, occs).getRoot();
        else
            result = tr;

        assert(!cache.contains(tr));
        cache.insert(tr, result);
    }

    fc.setRoot(cache[f]);
    return fc;
}
#endif

//
// Replace subtrees consisting only of ands / ors with a single and / or term.
// Search a maximal section of the tree consisting solely of ands / ors.  The
// root of this subtree is called and / or root.  Collect the subtrees rooted at
// the leaves of this section, and create a new and / or term with the leaves as
// arguments and the parent of the and / or tree as the parent.
//
// However, we will do this in a clever way so that if a certain
// term appears as a child in more than one term, we will not flatten
// that structure.
//
MainSolver::FContainer MainSolver::propFlatten(MainSolver::FContainer fc)
{
#ifdef PEDANTIC_DEBUG
    cerr << "; COMPUTE INCOMING EDGES" << endl;
#endif

    PTRef top = fc.getRoot();
    vec<pi> qu;
    qu.push(pi(top));
    Map<PTRef,int,PTRefHash> occs;
    vec<PTRef> terms;
#ifdef PEDANTIC_DEBUG
    VecMap<PTRef,PTRef,PTRefHash > parents;
#endif

    while (qu.size() != 0) {
        int ci = qu.size() - 1;
#ifdef PEDANTIC_DEBUG
        cerr << "Processing " << logic.printTerm(qu[ci].x) << " (" << qu[ci].x.x << ")" << endl;
#endif
//        assert(!occs.contains(qu[ci].x));
        if (occs.contains(qu[ci].x)) {
            // fires if a term has two occurrences of the same atom
#ifdef PEDANTIC_DEBUG
            cerr << "Processed before: " << logic.printTerm(qu[ci].x);
#endif
            occs[qu[ci].x]++;
            qu.pop();
            continue;
        }
        bool unprocessed_children = false;
#ifdef ENABLE_SHARING_BUG
        if (logic.isBooleanOperator(qu[ci].x))
#else
        if (logic.isBooleanOperator(qu[ci].x) && qu[ci].done == false)
#endif
        {
            Pterm& t = logic.getPterm(qu[ci].x);
            for (int i = 0; i < t.size(); i++) {
                PTRef cr = t[i];
                if (!occs.contains(cr)) {
                    unprocessed_children = true;
                    qu.push(pi(cr));
                    vec<PTRef> tmp;
                    tmp.push(qu[ci].x);
#ifdef PEDANTIC_DEBUG
                    parents.insert(cr,tmp);
#endif
                }
                else {
#ifdef PEDANTIC_DEBUG
                    Pterm& c = logic.getPterm(cr);
                    cerr << "Node id " << c.getId() << " Processed before 2: " << logic.printTerm(cr) << endl;
                    cerr << "Current parent is " << logic.printTerm(qu[ci].x) << endl;
#endif
                    occs[cr]++;
#ifdef PEDANTIC_DEBUG
                    parents[cr].push(qu[ci].x);
                    cerr << " has parents" << endl;
                    for (int i = 0; i < parents[cr].size(); i++)
                        cerr << "  - " << logic.getPterm(parents[cr][i]).getId() << endl;
#endif
                }
            }
            qu[ci].done = true;
        }
        if (unprocessed_children)
            continue;
        assert(!occs.contains(qu[ci].x));
        occs.insert(qu[ci].x, 1);
        terms.push(qu[ci].x);
        qu.pop();
    }

#ifdef ENABLE_SHARING_BUG
    fc = rewriteMaxArity(fc.getRoot(), occs);
#else

    vec<PtChild> and_roots;
    vec<PtChild> or_roots;
    Map<PTRef,PTRef,PTRefHash,Equal<PTRef> > parent;

    PTRef root = fc.getRoot();

    vec<PtChild> mainq;
    mainq.push(PtChild(root, PTRef_Undef, -1));
    parent.insert(root, PTRef_Undef);
    Map<PTRef, PTRef, PTRefHash> processed; // To reuse duplicate terms

    while (mainq.size() != 0) {
        // Find the and- or or-roots
        while (mainq.size() != 0) {
            PtChild ptc = mainq.last(); mainq.pop();
            Pterm& t = logic.getPterm(ptc.tr);
            if (logic.isAnd(ptc.tr))
                and_roots.push(ptc);
            else if (logic.isOr(ptc.tr))
                or_roots.push(ptc);

            else
                for (int i = t.size()-1; i >= 0; i--)
//                for (int i = 0; i < t.size(); i++)
                    if (!parent.contains(t[i])) {
                        assert(logic.getPterm(ptc.tr).size() > i);
                        mainq.push(PtChild(t[i], ptc.tr, i));
                        parent.insert(t[i], ptc.tr);
                    }
        }

        // Process starting from them
        while (and_roots.size() + or_roots.size() != 0) {
            if (and_roots.size() != 0) {
                bool changed = false;  // Did we find ands to collapse
                vec<PTRef> args;
                vec<PTRef> queue;
                vec<PtChild> new_ors;
                vec<PtChild> new_ands;
                vec<PtChild> new_mains;

                PtChild and_root = and_roots.last(); and_roots.pop();

#ifdef PEDANTIC_DEBUG
                if (and_root.parent != PTRef_Undef)
                    assert(logic.getPterm(and_root.parent).size() > and_root.pos);
//                cerr << "and root: " << logic.printTerm(and_root.tr) << endl;
#endif
                Pterm& and_root_t = logic.getPterm(and_root.tr);
 //               for (int i = 0; i < and_root_t.size(); i++)
                for (int i = and_root_t.size()-1; i >= 0; i--)
                    queue.push(and_root_t[i]);

                while (queue.size() != 0) {
                    PTRef tr = queue.last(); queue.pop();
                    assert(tr != and_root.tr);
                    Pterm& t = logic.getPterm(tr);
                    if (logic.isAnd(tr)) {
                        if (occs[tr] > 1) {
                            // This tr is used elsewhere.
                            // Open it once, store its opened version and
                            // use the opened term next time it is seen.
                            if (processed.contains(tr)) {
                                args.push(processed[tr]);
                                changed = true;
                            } else { // The new and root
                                args.push(tr);
                            }
#ifdef PEDANTIC_DEBUG
                            cerr << " Using shared structure (" << occs[tr];
                            PTRef tmp_tr;
                            if (processed.contains(tr))
                                tmp_tr = processed[tr];
                            else
                                tmp_tr = tr;
                            char* name = logic.printTerm(tmp_tr);
                            cerr << " * " << name << endl;
                            ::free(name);
#endif
                        } else {
                            changed = true; // We need a new and
                            for (int i = t.size()-1; i >= 0; i--)
//                            for (int i = 0; i < t.size(); i++)
                                queue.push(t[i]);
                        }
                    } else
                        args.push(tr);
                }

                PTRef par_tr;

                // Do not duplicate if nothing changed
                if (changed) {
                    par_tr = logic.mkAnd(args);
                    for (int i = 0; i < args.size(); i++) {
                        if (logic.isAnd(args[i]) && occs[args[i]] < 2)
                            and_roots.push(PtChild(args[i], par_tr, i));
                        else if (logic.isOr(args[i]))
                            or_roots.push(PtChild(args[i], par_tr, i));
                        else
                            mainq.push(PtChild(args[i], par_tr, i));
                    }
                    if (occs.contains(par_tr))
                        occs[par_tr]++;
                    else
                        occs.insert(par_tr, 1);
                } else
                    par_tr = and_root.tr;

                processed.insert(and_root.tr, par_tr);

                if (and_root.parent != PTRef_Undef) {
//                    assert(logic.getPterm(and_root.parent).size() > and_root.pos);
                    logic.getPterm(and_root.parent)[and_root.pos] = par_tr;
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(and_root.parent) << endl;
#endif
                }
                else
                    fc.setRoot(par_tr);
#ifdef PEDANTIC_DEBUG
//                cerr << " => " << logic.printTerm(par_tr) << endl;
#endif
            }

            if (or_roots.size() != 0) {
                bool changed = false;  // Did we find ors to collapse
                vec<PTRef> args;
                vec<PTRef> queue;
                vec<PtChild> new_ors;
                vec<PtChild> new_ands;
                vec<PtChild> new_mains;

                PtChild or_root = or_roots.last(); or_roots.pop();

#ifdef PEDANTIC_DEBUG
                if (or_root.parent != PTRef_Undef)
                    assert(logic.getPterm(or_root.parent).size() > or_root.pos);
//                cerr << "or root: " << logic.printTerm(or_root.tr) << endl;
#endif
                Pterm& or_root_t = logic.getPterm(or_root.tr);
//                for (int i = 0; i < or_root_t.size(); i++)
                for (int i = or_root_t.size()-1; i >= 0; i--)
                    queue.push(or_root_t[i]);

                while (queue.size() != 0) {
                    PTRef tr = queue.last(); queue.pop();
                    assert(tr != or_root.tr);
                    Pterm& t = logic.getPterm(tr);
                    if (logic.isOr(tr)) { // We need a new or
                        if (occs[tr] > 1) {
                            // This tr is used elsewhere.
                            // Open it once, store its opened version and
                            // use the opened term next time it is seen.
                            if (processed.contains(tr)) {
                                args.push(processed[tr]);
                                changed = true; // We need a new or
                            } else { // The new or root
                                args.push(tr);
                            }
#ifdef PEDANTIC_DEBUG
                            cerr << " Using shared structure (" << occs[tr];
                            PTRef tmp_tr;
                            if (processed.contains(tr))
                                tmp_tr = processed[tr];
                            else
                                tmp_tr = tr;
                            char* name = logic.printTerm(tmp_tr);
                            cerr << " * " << name << endl;
                            ::free(name);
#endif
                        } else {
                            changed = true; // We need a new or
                            for (int i = t.size()-1; i >= 0; i--)
//                            for (int i = 0; i < t.size(); i++)
                                queue.push(t[i]);
                        }
                    } else
                        args.push(tr);
                }

                PTRef par_tr;

                // Do not duplicate if nothing changed
                if (changed) {
                    par_tr = logic.mkOr(args);
                    for (int i = 0; i < args.size(); i++) {
                        if (logic.isOr(args[i]) && occs[args[i]] < 2)
                            or_roots.push(PtChild(args[i], par_tr, i));
                        else if (logic.isAnd(args[i]))
                            and_roots.push(PtChild(args[i], par_tr, i));
                        else
                            mainq.push(PtChild(args[i], par_tr, i));
                    }
                    if (occs.contains(par_tr))
                        occs[par_tr]++;
                    else
                        occs.insert(par_tr, 1);
                } else
                    par_tr = or_root.tr;

                processed.insert(or_root.tr, par_tr);

                if (or_root.parent != PTRef_Undef) {
//                    assert(logic.getPterm(or_root.parent).size() > or_root.pos);
                    logic.getPterm(or_root.parent)[or_root.pos] = par_tr;
#ifdef PEDANTIC_DEBUG
                    cerr << logic.printTerm(or_root.parent) << endl;
#endif
                }
                else
                    fc.setRoot(par_tr);

#ifdef PEDANTIC_DEBUG
//                cerr << " => " << logic.printTerm(par_tr) << endl;
#endif
            }
        }
    }
#endif
    return fc;
}

//
// Merge terms with shared signatures in egraph representation and remove redundancies in
// equalities and disequalities
//
MainSolver::FContainer MainSolver::simplifyEqualities(vec<PtChild>& terms)
{
#ifdef PEDANTIC_DEBUG
    for (int i = 0; i < terms.size(); i++) {
        PtChild& ptc = terms[i];
        // XXX The terms in here might have invalid symbols for some reason.
        assert(logic.hasSym(logic.getPterm(ptc.tr).symb()));
    }
#endif
    PTRef root = terms[terms.size()-1].tr;
    for (int i = 0; i < terms.size(); i++) {
        PtChild& ptc = terms[i];
        PTRef tr = ptc.tr;
        if (logic.isTheoryTerm(tr) && logic.getTerm_true() != tr && logic.getTerm_false() != tr) {
            if (logic.isEquality(tr)) {
                if (uf_solver.simplifyEquality(ptc, true)) {
                    // the root of the formula is trivially true
                    root = logic.getTerm_true();
                    break;
                }

#ifdef PEDANTIC_DEBUG
                if (ptc.parent != PTRef_Undef && tr != logic.getPterm(ptc.parent)[ptc.pos]) {
                    cerr << "Simplified equality " << logic.printTerm(tr) << endl;
                    cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
                }
#endif
            }
            else if (logic.isDisequality(tr)) {
//                cerr << "Simplifying disequality " << logic.printTerm(tr) << endl;
                uf_solver.simplifyDisequality(ptc);
//                cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
            }
            uf_solver.declareTerm(ptc);
        }
    }
    return FContainer(root);
}

/*
sstat MainSolver::insertTermRoot(PTRef root, char** msg) {
    if (logic.getSort(root) != logic.getSort_bool()) {
        asprintf(msg, "Top-level assertion sort must be %s, got %s",
                 Logic::s_sort_bool, logic.getSort(logic.getSort(root)->getCanonName());
        return s_Error;
    }

    sstat state;
    lbool ts_state;
    vec<PtChild> terms;
#ifdef PEDANTIC_DEBUG
    vec<PTRef> glue_terms;
#endif

    // Framework for handling different logic related simplifications.
    // For soundness it is important to run this until closure
    while (true){
        if (!tlp.insertBindings(root)) {
            // insert an artificial unsatisfiable problem
            ts.cnfizeAndGiveToSolver(logic.mkNot(logic.getTerm_true()));
            state = s_False; goto end; }

        if (!tlp.substitute(root)) break;
    }
    // cnfization of the formula
    // Get the egraph data structure for instance from here
    // Terms need to be purified before cnfization?


    getTermList<PtChild>(root, terms, logic);

    if (terms.size() > 0) {
        root = ts.expandItes(terms);
        terms.clear();
        getTermList(root, terms, logic);
    }

    for (int i = terms.size()-1; i >= 0; i--) {
        PtChild& ptc = terms[i];
        PTRef tr = ptc.tr;
        if (logic.isTheoryTerm(tr) && logic.getTerm_true() != tr && logic.getTerm_false() != tr) {
            if (logic.isEquality(tr)) {
#ifdef PEDANTIC_DEBUG
                cerr << "Simplifying equality " << logic.printTerm(tr) << endl;
#endif
                if (uf_solver.simplifyEquality(ptc, true)) {
                    // the root of the formula is trivially true
                    root = logic.getTerm_true();
                    break;
                }

#ifdef PEDANTIC_DEBUG
                if (ptc.parent != PTRef_Undef)
                    cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
#endif
            }
            else if (logic.isDisequality(tr)) {
//                cerr << "Simplifying disequality " << logic.printTerm(tr) << endl;
                uf_solver.simplifyDisequality(ptc);
//                cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
            }
            uf_solver.declareTerm(ptc);
        }
    }

//    cerr << logic.printTerm(tr);
    ts_state = ts.cnfizeAndGiveToSolver(root);
#ifdef PEDANTIC_DEBUG
    for (int i = 0; i < sat_solver.n_occs.size(); i++) {
        if (sat_solver.n_occs[i] == 0)
            cerr << "No occurrences of var " << i
                 << " term " << logic.printTerm(tmap.varToTerm[i])
                 << endl;
    }
#endif
    if (ts_state == l_False)
        state = s_False;
#ifdef PEDANTIC_DEBUG
    for (int i = 0; i < glue_terms.size(); i++)
        cerr << "Glue term: " << logic.printTerm(glue_terms[i]) << endl;
#endif
end:
    if (state == s_False) {
        asprintf(msg, "; The formula is trivially unsatisfiable");
    }
    return state;
}
*/
