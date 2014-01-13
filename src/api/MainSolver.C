#include "MainSolver.h"
#include "simplifiers/TopLevelPropagate.h"

void MainSolver::getTermList(PTRef tr, vec<PtChild>& list_out) {
    vec<PTRef> queue;

    queue.push(tr);
    list_out.push(PtChild(tr, PTRef_Undef, -1));

    while (queue.size() > 0) {
        tr = queue.last();
        queue.pop();
        Pterm& pt = logic.getPterm(tr);
        for (int i = 0; i < pt.size(); i++) {
            queue.push(pt[i]);
            list_out.push(PtChild(pt[i], tr, i));
        }
    }
}

sstat MainSolver::insertTermRoot(PTRef root, char** msg) {
    if (logic.getSym(logic.getPterm(root).symb()).rsort() != logic.getSortRef(Logic::s_sort_bool)) {
        asprintf(msg, "Top-level assertion sort must be %s, got %s",
                 Logic::s_sort_bool,
                 logic.getSort(logic.getSym(logic.getPterm(root).symb()).rsort())->getCanonName());
        return s_Error;
    }
    // Framework for handling different logic related simplifications?
    // cnfization of the formula
    // Get the egraph data structure for instance from here
    // Terms need to be purified before cnfization?

    vec<PtChild> terms;
    getTermList(root, terms);

    if (terms.size() > 0) {
        root = ts.expandItes(terms);
        terms.clear();
        getTermList(root, terms);
    }

    for (int i = terms.size()-1; i >= 0; i--) {
        PtChild ptc = terms[i];
        PTRef tr = ptc.tr;
        if (logic.isTheoryTerm(tr) && logic.getTerm_true() != tr && logic.getTerm_false() != tr) {
            if (logic.isEquality(tr)) {
#ifdef PEDANTIC_DEBUG
                cerr << "Simplifying equality " << logic.printTerm(tr) << endl;
#endif
                uf_solver.simplifyEquality(terms[i], true);
#ifdef PEDANTIC_DEBUG
                if (ptc.parent != PTRef_Undef)
                    cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
#endif
            }
            else if (logic.isDisequality(tr)) {
//                cerr << "Simplifying disequality " << logic.printTerm(tr) << endl;
                uf_solver.simplifyDisequality(terms[i]);
//                cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
            }
            uf_solver.declareTerm(ptc);
        }
    }

    TopLevelPropagator tlp = TopLevelPropagator(logic, ts);
    tlp.insertBinings(root);

//    cerr << logic.printTerm(tr);
#ifdef PEDANTIC_DEBUG
    vec<PTRef> glue_terms;
#endif
    sstat state;
    lbool ts_state = ts.cnfizeAndGiveToSolver(root);
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
    if (state == s_False) {
        asprintf(msg, "; The formula is trivially unsatisfiable");
    }
    return state;
}
