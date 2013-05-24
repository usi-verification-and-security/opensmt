#include "MainSolver.h"

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

sstat MainSolver::insertTermRoot(PTRef tr, char** msg) {
    if (logic.getSym(logic.getPterm(tr).symb()).rsort() != logic.getSortRef(Logic::s_sort_bool)) {
        asprintf(msg, "Top-level assertion sort must be %s, got %s",
                 Logic::s_sort_bool,
                 logic.getSort(logic.getSym(logic.getPterm(tr).symb()).rsort())->getCanonName());
        return s_Error;
    }
    // Framework for handling different logic related simplifications?
    // cnfization of the formula
    // Get the egraph data structure for instance from here
    // Terms need to be purified before cnfization?

    vec<PtChild> terms;
    getTermList(tr, terms);

    if (terms.size() > 0)
        tr = ts.expandItes(terms);

    vec<PTRef> bools;
    vec<PTRef> bool_roots;
    bool_roots.push(tr);
    sstat state;


    while (bool_roots.size() != 0) {


        vec<PtPair> ites;
        tr = bool_roots.last();
        bools.push(tr);
        bool_roots.pop();
        lbool val = uf_solver.simplifyAndAddTerms(tr, ites, bools);
        if (val == l_True) tr = logic.getTerm_true();
        else if (val == l_False) tr = logic.getTerm_false();

//        ts.expandItes(ites, bool_roots);

    }
#ifdef PEDANTIC_DEBUG
    vec<PTRef> glue_terms;
#endif
    while (bools.size() != 0) {
        PTRef ctr = bools.last();
        bools.pop();
        lbool ts_state = ts.cnfizeAndGiveToSolver(ctr);
        if (ts_state == l_False) {
            state = s_False; break; }
    }
#ifdef PEDANTIC_DEBUG
    for (int i = 0; i < glue_terms.size(); i++)
        cerr << "Glue term: " << ptstore.printTerm(glue_terms[i]) << endl;
#endif
    if (state == s_False) {
        asprintf(msg, "The formula is trivially unsatisfiable");
    }
    return state;
}
