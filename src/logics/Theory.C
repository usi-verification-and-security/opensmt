#include "logics/Theory.h"
//#include "logics/Logic.h"

bool Theory::computeSubstitutions(PTRef root, PTRef& root_out)
{
    if (!config.do_substitutions() || config.produce_inter()) {
        root_out = root;
        return true;
    }
    // The substitution of facts together with the call to simplifyTree
    // ensures that no fact is inserted twice to facts.
    vec<PtAsgn> facts;
    // l_True : exists and is valid
    // l_False : exists but has been disabled to break symmetries
    Map<PTRef,PtAsgn,PTRefHash> substs;
    Logic& logic = getLogic();
    // fixpoint
    while (true) {
        logic.collectFacts(root, facts);
        lbool res = logic.retrieveSubstitutions(facts, substs);
        if (res != l_Undef) root = (res == l_True ? logic.getTerm_true() : logic.getTerm_false());
        PTRef new_root;
        bool cont = logic.varsubstitute(root, substs, new_root);
        root = new_root;
        if (!cont) break;
    }
#ifdef SIMPLIFY_DEBUG
    vec<PTRef> keys_dbg;
    substs.getKeys(keys_dbg);
    cerr << "Number of gaussian substitutions: " << keys_dbg.size() << endl;
    printf("Substitutions:\n");
    for (int i = 0; i < keys_dbg.size(); i++) {
        printf("  %s -> %s (%s)\n", logic.printTerm(keys_dbg[i]), logic.printTerm(substs[keys_dbg[i]].tr), substs[keys_dbg[i]].sgn == l_True ? "enabled" : "disabled");
    }
#endif
    vec<PTRef> args;
    for (int i = 0; i < facts.size(); i++) {
        assert(facts[i].sgn == l_True || logic.isBoolAtom(facts[i].tr));
        if (logic.isTheoryEquality(facts[i].tr))
            args.push(facts[i].tr);
    }

    // Remove duplicates from args
    sort(args);
    PTRef p = PTRef_Undef;
    int i = 0, j = 0;
    for (; i < args.size(); i++) {
        if (args[i] != p) args[j++] = args[i];
        p = args[i];
    }
    args.shrink(i-j);

    // Feed the top-level facts to the theory solver to check for
    // unsatisfability
    vec<DedElem> deds;
    deds.push(DedElem_Undef); // True
    deds.push(DedElem_Undef); // False
    Map<PTRef,int,PTRefHash> refs;
    TSolverHandler * th = getTSolverHandler_new(deds);
    refs.insert(logic.getTerm_true(), 0);
    refs.insert(logic.getTerm_false(), 1);
    th->fillTmpDeds(root, refs);

    for (int i = 0; i < args.size(); i++)
        th->fillTmpDeds(args[i], refs);

    bool no_conflict = true;
    for (int i = 0; i < args.size(); i++)
        if (!th->assertLit_special(PtAsgn(args[i], l_True))) {
            no_conflict = false;
            break; }

    root_out = root;

    vec<PTRef> keys;
    refs.getKeys(keys);
    for (int i = 0; i < keys.size(); i++)
        logic.getPterm(keys[i]).clearVar();

    bool result = no_conflict && th->check(true);

    delete th;
    return result;
}
