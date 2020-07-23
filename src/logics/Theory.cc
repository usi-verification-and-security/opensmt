#include "Theory.h"
//#include "MainSolver.h"
//#include "logics/Logic.h"


// The Collate function is constructed from all frames up to the current
// one and will be used to simplify the formulas in the current frame
// formulas[curr].
// (1) Construct the collate function as a conjunction of formulas up to curr.
// (2) From the coll function compute units_{curr}
// (3) Use units_1 /\ ... /\ units_{curr} to simplify formulas[curr]
//
// In addition we add the transitivie equalities as a further
// simplification (critical for the eq_diamond instances in QF_UF of
// smtlib).
//
PTRef Theory::getCollateFunction(const vec<PFRef> & formulas, int curr)
{
    assert(curr < formulas.size());
    // XXX
//    getLogic().dumpHeaderToFile(std::cout);
//    getLogic().dumpFormulaToFile(std::cout, pfstore[formulas[1]].formulas[0]);
    vec<PTRef> coll_f_args;
    // compute coll_f as (a_1^0 /\ ... /\ a_{n_1}^0) /\ ... /\ (a_1^{curr} /\ ... /\ a_{n_k}^{curr})
    for (int i = 0; i <= curr; i++)
    {
        for (int j = 0; j < pfstore[formulas[i]].size(); j++)
            coll_f_args.push(pfstore[formulas[i]][j]);
    }
    return getLogic().mkAnd(coll_f_args);
}

namespace{
    void substitutionsTransitiveClosure(Logic & logic, Map<PTRef, PtAsgn, PTRefHash> & substs) {
        bool changed = true;
//        vec<Map<PTRef, PtAsgn, PTRefHash>::Pair> keyvals;
        vec<PTRef> keys;
        substs.getKeys(keys);
        std::vector<char> notChangedElems(keys.size(), 0); // True if not changed in last iteration, initially False
        while (changed) {
            changed = false;
            for (int i = 0; i < keys.size(); ++i) {
                auto key = keys[i];
                auto val = substs[key];
                if (val.sgn != l_True || notChangedElems[i]) { continue; }
                PTRef newVal = PTRef_Undef;
                PTRef oldVal = val.tr;
                logic.varsubstitute(oldVal, substs, newVal);
                if (oldVal != newVal) {
                    changed = true;
                    substs[key] = PtAsgn(newVal, l_True);
                }
                else {
                    notChangedElems[i] = 1;
                }
            }
        }
    }
}


// Given coll_f = (R_1 /\ ... /\ R_{curr-1}) /\ (U_1 /\ ... /\ U_{curr-1}) /\ P_{curr},
// compute U_{curr}.  Place U_{curr} to frame and simplify
// the problem P_{curr} using (U_1 /\ ... /\ U_{curr}) resulting in
// R_{curr}.
// If x = f(Y) is a newly found substitution and there is a lower frame F containing x, add x = f(Y) to R_{curr}.
//
bool Theory::computeSubstitutions(const PTRef coll_f, const vec<PFRef>& frames, const int curr)
{
    if (!config.do_substitutions() || config.produce_inter()) {
        pfstore[frames[curr]].root = getLogic().mkAnd(pfstore[frames[curr]].formulas);
        return true;
    }
    assert(config.do_substitutions() && !config.produce_inter());
    assert(pfstore[frames[curr]].units.elems() == 0);
    // MB: We are going to simplify coll_f and it already contains the current frame
    PTRef root = coll_f;
    // l_True : exists and is valid
    // l_False : exists but has been disabled to break symmetries
    vec<Map<PTRef,lbool,PTRefHash>*> prev_units;
    vec<PtAsgn> prev_units_vec;
    for (int i = 0; i < curr; i++) {
        prev_units.push(&(pfstore[frames[i]].units));
        vec<Map<PTRef,lbool,PTRefHash>::Pair> tmp;
        pfstore[frames[i]].units.getKeysAndVals(tmp);
        for (auto const & entry : tmp) {
            prev_units_vec.push(PtAsgn(entry.key, entry.data));
        }
    }

    Map<PTRef,PtAsgn,PTRefHash> allsubsts;
    vec<PtAsgn> all_units_vec;
    vec<PtAsgn> current_units_vec;
    prev_units_vec.copyTo(all_units_vec);
    prev_units_vec.copyTo(current_units_vec);
    // This computes the new unit clauses to curr_frame.units until closure
    while (true) {
        // update the current simplification formula
        PTRef simp_formula = root;
        Map<PTRef,lbool,PTRefHash> new_units;
        vec<Map<PTRef,lbool,PTRefHash>::Pair> new_units_vec;
        // Get U_i
        getLogic().getNewFacts(simp_formula, prev_units, new_units);
        // Add the newly obtained units to the list of all substitutions
        // Clear the previous units
        new_units.getKeysAndVals(new_units_vec);
        for (int i = 0; i < new_units_vec.size(); i++) {
            Map<PTRef,lbool,PTRefHash>::Pair unit = new_units_vec[i];
            if (!pfstore[frames[curr]].units.has(unit.key)) {
                pfstore[frames[curr]].units.insert(unit.key, unit.data);
                all_units_vec.push(PtAsgn(unit.key, unit.data));
                current_units_vec.push(PtAsgn(unit.key, unit.data));
            }
        }
        Map<PTRef,PtAsgn,PTRefHash> newsubsts;
        lbool res = getLogic().retrieveSubstitutions(current_units_vec, newsubsts);
        current_units_vec.clear();
        substitutionsTransitiveClosure(getLogic(), newsubsts);
        if (res != l_Undef)
            root = (res == l_True ? getLogic().getTerm_true() : getLogic().getTerm_false());
        PTRef new_root;
        bool cont = getLogic().varsubstitute(root, newsubsts, new_root);
        // remember the substitutions
        vec<Map<PTRef,PtAsgn,PTRefHash>::Pair> newsubsts_vec;
        newsubsts.getKeysAndVals(newsubsts_vec);
        for (int i = 0; i < newsubsts_vec.size(); ++i) {
            PTRef key = newsubsts_vec[i].key;
            if (!allsubsts.has(key) && newsubsts_vec[i].data.sgn == l_True) {
                allsubsts.insert(key, newsubsts_vec[i].data);
            }
        }
        root = new_root;

        if (!cont) break;
    }
#ifdef SIMPLIFY_DEBUG
    cerr << "Number of substitutions: " << allsubsts.elems() << endl;
    vec<Map<PTRef,PtAsgn,PTRefHash>::Pair> subst_vec;
    substs.getKeysAndVals(subst_vec);
    printf("Substitutions:\n");
    for (int i = 0; i < subst_vec.size(); i++) {
        PTRef source = subst_vec[i].key;
        PTRef target = subst_vec[i].data.tr;
        lbool sgn = subst_vec[i].data.sgn;
        printf("  %s -> %s (%s)\n", getLogic().printTerm(source), getLogic().printTerm(target), sgn == l_True ? "enabled" : "disabled");
    }
#endif
    assert(std::all_of(all_units_vec.begin(), all_units_vec.end(),
            [this](PtAsgn ptasgn) { return ptasgn.sgn == l_True || getLogic().isBoolAtom(ptasgn.tr); }));

    pfstore[frames[curr]].root = root;

    // Traverse frames[curr].root to see all the variables.
    vec<PTRef> queue;
    Map<PTRef,PTRef,PTRefHash> tr_map;
    Map<PTRef,bool,PTRefHash> processed;
    queue.push(pfstore[frames[curr]].root);
    while (queue.size() != 0)
    {
        PTRef tr = queue.last();
        if (processed.has(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        Pterm& t = getLogic().getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            PTRef cr = t[i];
            if (!processed.has(cr)) {
                unprocessed_children = true;
                queue.push(cr);
            }
        }
        if (unprocessed_children) continue;
        if (getLogic().isVar(tr))
        {
#ifdef PEDANTIC_DEBUG
            char* name = getLogic().printTerm(tr);
            printf("Found a variable %s\n", name);
            free(name);
#endif
            pfstore[frames[curr]].addSeen(tr);
        }
        processed.insert(tr, true);
        queue.pop();
    }

    // Check the previous frames to see whether a substitution needs to
    // be inserted to frames[curr].root.
    vec<Map<PTRef,PtAsgn,PTRefHash>::Pair> substitutions;
    allsubsts.getKeysAndVals(substitutions);
    for (int i = 0; i < substitutions.size(); i++)
    {
        Map<PTRef,PtAsgn,PTRefHash>::Pair& p = substitutions[i];
        PTRef var = p.key;
        for (int j = 0; j < curr; j ++)
        {
            if (pfstore[frames[j]].isSeen(var))
            {
                // The substitution needs to be added to the root
                // formula
                PTRef subst_tr = getLogic().mkEq(var, p.data.tr);
                subst_tr = p.data.sgn == l_True ? subst_tr : getLogic().mkNot(subst_tr);
                pfstore[frames[curr]].root = getLogic().mkAnd(subst_tr, pfstore[frames[curr]].root);
#ifdef PEDANTIC_DEBUG
                char* name_var = getLogic().printTerm(var);
                char* name_exp = getLogic().printTerm(p.data.tr);
                char* name_sub = getLogic().printTerm(subst_tr);
                printf("Found a substitution %s / %s with occurrence higher in the stack.\n  => Adding the formula %s to the root formula of this frame.\n",
                        name_var, name_exp, name_sub);
                free(name_var);
                free(name_exp);
                free(name_sub);
#endif
                continue; // Go to the next substitution
            }
        }
    }
    getTSolverHandler().setSubstitutions(allsubsts);
    return true;
}

/**
 * Purify the terms of the frame.
 * Example 1:
 * root := f(c, a) != f(true,b) /\ f(c, a) != f(false,b)
 *
 * after purification:
 * root := f(c, a) != f(true,b) /\ f(c, a) != f(false,b)
 * pured_atoms := c
 *
 * Example 2:
 * root  := f((c \/ d) /\ (c \/ -d) /\ (-c \/ d) /\ (-c \/ -d))
 * after purification:
 * root := f((c \/ d) /\ (c \/ -d) /\ (-c \/ d) /\ (-c \/ -d))
 * pured_atoms := (c \/ d) /\ (c \/ -d) /\ (-c \/ d) /\ (-c \/ -d)
 *
 * @param frames
 * @param i
 */
void
Theory::purify(const vec<PFRef>& frames, int i)
{

}

void
Theory::printFramesAsQuery(const vec<PFRef> & frames, std::ostream & s)
{
    getLogic().dumpHeaderToFile(s);
    for (int i = 0; i < frames.size(); i++) {
        if (i > 0)
            s << "(push 1)\n";
        getLogic().dumpFormulaToFile(s, pfstore[frames[i]].root);
    }
    getLogic().dumpChecksatToFile(s);
}

PTRef Theory::getSubstitutionsFormulaFromUnits(Map<PTRef, lbool, PTRefHash> & unitsMap) {
    vec<Map<PTRef, lbool, PTRefHash>::Pair> units;
    unitsMap.getKeysAndVals(units);
    vec<PTRef> substs_vec;
    for (int i = 0; i < units.size(); i++) {
        if (units[i].data == l_True) {
            substs_vec.push(units[i].key);
        }
        else if (getLogic().isBoolAtom(units[i].key) && units[i].data == l_False) {
            substs_vec.push(getLogic().mkNot(units[i].key));
        }
    }
    PTRef substs_formula = getLogic().mkAnd(substs_vec);
    return substs_formula;
}

//MOVINGFROMHEADER
void Theory::setSubstitutions(Map<PTRef,PtAsgn,PTRefHash>& substs) { getTSolverHandler().setSubstitutions(substs); }

TermMapper&  LRATheory::getTmap() { return tmap; }
LRALogic&    LRATheory::getLogic()    { return lralogic; }
LRATHandler& LRATheory::getTSolverHandler() { return lratshandler; }

TermMapper&  LIATheory::getTmap() { return tmap; }
LIALogic&    LIATheory::getLogic()    { return lialogic; }
LIATHandler& LIATheory::getTSolverHandler() { return liatshandler; }

