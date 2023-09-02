#include "Theory.h"
#include "Substitutor.h"


Theory::SubstitutionResult Theory::computeSubstitutions(const PTRef fla)
{
    SubstitutionResult result;
    assert(config.do_substitutions() && !config.produce_inter());
    PTRef root = fla;
    // l_True : exists and is valid
    // l_False : exists but has been disabled to break symmetries
    Logic::SubstMap allsubsts;
    // This computes the new unit clauses to curr_frame.units until closure
    while (true) {
        // update the current simplification formula
        PTRef simp_formula = root;
        MapWithKeys<PTRef,lbool,PTRefHash> new_units;
        vec<PtAsgn> current_units_vec;
        // Get U_i
        bool rval = getLogic().getNewFacts(simp_formula, new_units);
        if (not rval) {
            return SubstitutionResult{{}, getLogic().getTerm_false()};
        }
        // Add the newly obtained units to the list of all substitutions
        // Clear the previous units
        const auto & new_units_vec = new_units.getKeys();
        for (PTRef key : new_units_vec) {
            current_units_vec.push(PtAsgn{key, new_units[key]});
        }

        auto [res, newsubsts] = getLogic().retrieveSubstitutions(current_units_vec);
        getLogic().substitutionsTransitiveClosure(newsubsts);


        // remember the substitutions for models
        for (PTRef key : newsubsts.getKeys()) {
            if (!allsubsts.has(key)) {
                const auto target = newsubsts[key];
                allsubsts.insert(key, target);
            }
        }

        if (res != l_Undef)
            root = (res == l_True ? getLogic().getTerm_true() : getLogic().getTerm_false());

        PTRef new_root = Substitutor(getLogic(), newsubsts).rewrite(root);

        bool cont = new_root != root;
        root = new_root;
        if (!cont) break;
    }
    result.result = root;
    result.usedSubstitution = std::move(allsubsts);
    return result;
}


PTRef Theory::flaFromSubstitutionResult(const Theory::SubstitutionResult & sr) {
    Logic & logic = getLogic();
    vec<PTRef> args;
    const auto & entries = sr.usedSubstitution.getKeys();
    for (auto entry : entries) {
        auto target = sr.usedSubstitution[entry];
        args.push(logic.mkEq(entry, target));
    }
    args.push(sr.result);
    return logic.mkAnd(std::move(args));
}

PTRef Theory::applySubstitutionBasedSimplificationIfEnabled(PTRef root) {
    return config.do_substitutions() ? flaFromSubstitutionResult(computeSubstitutions(root)) : root;
}
