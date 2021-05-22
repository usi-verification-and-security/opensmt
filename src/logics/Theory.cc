#include "Theory.h"
#include "Substitutor.h"
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


Theory::SubstitutionResult Theory::computeSubstitutions(const PTRef fla)
{
    SubstitutionResult result;
    assert(config.do_substitutions() && !config.produce_inter());
    PTRef root = fla;
    // l_True : exists and is valid
    // l_False : exists but has been disabled to break symmetries
    MapWithKeys<PTRef,PtAsgn,PTRefHash> allsubsts;
    // This computes the new unit clauses to curr_frame.units until closure
    while (true) {
        // update the current simplification formula
        PTRef simp_formula = root;
        MapWithKeys<PTRef,lbool,PTRefHash> new_units;
        vec<PtAsgn> current_units_vec;
        // Get U_i
        getLogic().getNewFacts(simp_formula, new_units);
        // Add the newly obtained units to the list of all substitutions
        // Clear the previous units
        const auto & new_units_vec = new_units.getKeys();
        for (PTRef key : new_units_vec) {
            current_units_vec.push(PtAsgn{key, new_units[key]});
        }

        MapWithKeys<PTRef,PtAsgn,PTRefHash> newsubsts;
        lbool res = getLogic().retrieveSubstitutions(current_units_vec, newsubsts);
        getLogic().substitutionsTransitiveClosure(newsubsts);
        if (res != l_Undef)
            root = (res == l_True ? getLogic().getTerm_true() : getLogic().getTerm_false());
        PTRef new_root = Substitutor(getLogic(), newsubsts).rewrite(root);
        bool cont = new_root != root;
        // remember the substitutions
        auto & newsubsts_vec(newsubsts.getKeys());
        for (PTRef key : newsubsts_vec) {
            const auto & el(newsubsts[key]);
            if (!allsubsts.has(key) && el.sgn == l_True) {
                allsubsts.insert(key, el);
            }
        }
        root = new_root;
        if (!cont) break;
    }
#ifdef SIMPLIFY_DEBUG
    cerr << "Number of substitutions: " << allsubsts.elems() << endl;
    vec<Map<PTRef,PtAsgn,PTRefHash>::Pair> subst_vec;
    allsubsts.getKeysAndVals(subst_vec);
    printf("Substitutions:\n");
    for (int i = 0; i < subst_vec.size(); i++) {
        PTRef source = subst_vec[i].key;
        PTRef target = subst_vec[i].data.tr;
        lbool sgn = subst_vec[i].data.sgn;
        printf("  %s -> %s (%s)\n", getLogic().printTerm(source), getLogic().printTerm(target), sgn == l_True ? "enabled" : "disabled");
    }
#endif
    result.result = root;
    std::swap(allsubsts, result.usedSubstitution);
    return result;
}

void
Theory::printFramesAsQuery(const vec<PFRef> & frames, std::ostream & s) const
{
    getLogic().dumpHeaderToFile(s);
    for (int i = 0; i < frames.size(); i++) {
        if (i > 0)
            s << "(push 1)\n";
        getLogic().dumpFormulaToFile(s, pfstore[frames[i]].root);
    }
    getLogic().dumpChecksatToFile(s);
}

PTRef Theory::flaFromSubstitutionResult(const Theory::SubstitutionResult & sr) {
    Logic & logic = getLogic();
    vec<PTRef> args;
    auto & entries = sr.usedSubstitution.getKeys();
    for (auto entry : entries) {
        auto target = sr.usedSubstitution[entry];
        assert(target.sgn == l_True);
        if (target.sgn == l_True) {
            args.push(logic.mkEq(entry, target.tr));
        }
    }
    args.push(sr.result);
    return logic.mkAnd(args);
}

