#include "MainSolver.h"
#include "TreeOps.h"

sstat MainSolver::simplifyFormulas(char** err_msg) {
    sstat  state;
    PTRef  root;
    // Think of something here to enable incrementality...
    if (!ts.solverEmpty()) {
        asprintf(err_msg, "Solver already contains a simplified problem.  Cannot continue for now");
        return s_Error; }

    root = logic.mkAnd(formulas);
    // Framework for handling different logic related simplifications.
    // For soundness it is important to run this until closure
    vec<PTRef> tlfacts;
    while (true) {
        if (!tlp.updateBindings(root, tlfacts)) {
            // insert an artificial unsatisfiable problem
            ts.cnfizeAndGiveToSolver(logic.mkNot(logic.getTerm_true()));
            state = s_False; goto end; }

        if (!tlp.substitute(root)) break;
    }
#ifdef PEDANTIC_DEBUG
    cerr << "Stored top level facts not to be simplified away: " << endl;
    for (int i = 0; i < tlfacts.size(); i++)
        cerr << logic.printTerm(tlfacts[i]) << endl;
#endif
    {
        // Add the top level facts to the formula
        tlfacts.push(root);
        root = logic.mkAnd(tlfacts);
        vec<PtChild> terms;
        FContainer fc(root);
        expandItes(fc, terms);
        fc = simplifyEqualities(terms);
        state = giveToSolver(fc.getRoot());
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
        getTermList<PtChild>(root, terms, logic);
    }
    fc.setRoot(root);
}

//
// Merge terms with shared signatures in egraph representation and remove redundancies in
// equalities and disequalities
//
MainSolver::FContainer MainSolver::simplifyEqualities(vec<PtChild>& terms)
{
    PTRef root = terms[0].tr;

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
