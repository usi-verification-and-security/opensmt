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
    for (int i = 0; i < curr+1; i++)
    {
        for (int j = 0; j < pfstore[formulas[i]].size(); j++)
            coll_f_args.push(pfstore[formulas[i]][j]);
    }
    return getLogic().mkAnd(coll_f_args);
}

//
// Given coll_f = (R_1 /\ ... /\ R_{curr-1}) /\ (U_1 /\ ... /\ U_{curr-1}) /\
// P_{curr}, compute U_{curr}.  Place U_{curr} to frame and simplify
// the problem P_{curr} using (U_1 /\ ... /\ U_{curr}) resulting in
// R_{curr}.
// If x = f(Y) is a newly found substitution and there is a lower frame F containing x, add x = f(Y) to R_{curr}.
//
bool Theory::computeSubstitutions(const PTRef coll_f, const vec<PFRef>& frames, const int curr)
{
    if (!config.do_substitutions() || config.produce_inter()) {
        vec<PTRef> curr_args;
        for (int i = 0; i < pfstore[frames[curr]].size(); i++)
            curr_args.push(pfstore[frames[curr]][i]);
        pfstore[frames[curr]].root = getLogic().mkAnd(curr_args);
        return true;
    }
    assert(config.do_substitutions() && !config.produce_inter());
    vec<PTRef> curr_args;
    const PushFrame& curr_frame = pfstore[frames[curr]];

    assert(curr_frame.units.elems() == 0);

    // root for the first iteration is P_{curr}
    for (int i = 0; i < curr_frame.size(); i++)
        curr_args.push(curr_frame[i]);
    PTRef root = getLogic().mkAnd(curr_args);

    // l_True : exists and is valid
    // l_False : exists but has been disabled to break symmetries

    vec<Map<PTRef,lbool,PTRefHash>*> prev_units;
    vec<PtAsgn> prev_units_vec;
    for (int i = 0; i < curr; i++) {
        prev_units.push(&(pfstore[frames[i]].units));
        vec<Map<PTRef,lbool,PTRefHash>::Pair> tmp;
        pfstore[frames[i]].units.getKeysAndVals(tmp);
        for (int i = 0; i < tmp.size(); i++)
            prev_units_vec.push(PtAsgn(tmp[i].key, tmp[i].data));
    }

    Map<PTRef,PtAsgn,PTRefHash> substs;
    vec<PtAsgn> all_units_vec;
    prev_units_vec.copyTo(all_units_vec);
    // This computes the new unit clauses to curr_frame.units until closure
    while (true) {
        // update the current simplification formula
        PTRef simp_formula = getLogic().mkAnd(coll_f, root);
        // Get U_i
        getLogic().getNewFacts(simp_formula, prev_units, pfstore[frames[curr]].units);
        // Add the newly obtained units to the list of all substitutions
        vec<Map<PTRef,lbool,PTRefHash>::Pair> new_units;
        // Clear the previous units
        all_units_vec.shrink(all_units_vec.size() - prev_units_vec.size());
        pfstore[frames[curr]].units.getKeysAndVals(new_units);
        for (int i = 0; i < new_units.size(); i++) {
            Map<PTRef,lbool,PTRefHash>::Pair unit = new_units[i];
            all_units_vec.push(PtAsgn(unit.key, unit.data));
        }
        lbool res = getLogic().retrieveSubstitutions(all_units_vec, substs);
        if (res != l_Undef)
            root = (res == l_True ? getLogic().getTerm_true() : getLogic().getTerm_false());
        PTRef new_root;
        bool cont = getLogic().varsubstitute(root, substs, new_root);
        root = new_root;
        if (!cont) break;
    }
#ifdef SIMPLIFY_DEBUG
    cerr << "Number of substitutions: " << all_units_vec.size() << endl;
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
    vec<PTRef> args;
    for (int i = 0; i < all_units_vec.size(); i++) {
        assert(all_units_vec[i].sgn == l_True || getLogic().isBoolAtom(all_units_vec[i].tr));
        if (getLogic().isTheoryEquality(all_units_vec[i].tr))
            args.push(all_units_vec[i].tr);
    }


    // Feed the top-level facts to the theory solver to check for
    // unsatisfability
    vec<DedElem> deds;
    deds.push(DedElem_Undef); // True
    deds.push(DedElem_Undef); // False
    Map<PTRef,int,PTRefHash> refs;
    TSolverHandler * th = getTSolverHandler_new(deds);
    refs.insert(getLogic().getTerm_true(), 0);
    refs.insert(getLogic().getTerm_false(), 1);
    th->fillTmpDeds(root, refs);

    for (int i = 0; i < args.size(); i++)
        th->fillTmpDeds(args[i], refs);

    bool no_conflict = true;
    for (int i = 0; i < args.size(); i++) {
        if (!th->assertLit_special(PtAsgn(args[i], l_True))) {
            no_conflict = false;
            break;
        }
    }

    bool result = no_conflict && (th->check(true) == TRes::SAT);

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
    substs.getKeysAndVals(substitutions);
    for (int i = 0; i < substitutions.size(); i++)
    {
        Map<PTRef,PtAsgn,PTRefHash>::Pair& p = substitutions[i];
        PTRef var = p.key;
        for (int i = 0; i < curr; i ++)
        {
            if (pfstore[frames[i]].isSeen(var))
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
    getTSolverHandler().setSubstitutions(substs);
    delete th;
    return result;
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

//MOVINGFROMHEADER

void PushFrameAllocator::moveTo(PushFrameAllocator& to) {
    to.id_counter = id_counter;
    RegionAllocator<uint32_t>::moveTo(to); }
PFRef PushFrameAllocator::alloc()
{
    uint32_t v = RegionAllocator<uint32_t>::alloc(sizeof(PushFrame));
    PFRef r = {v};
    new (lea(r)) PushFrame(id_counter++);
    return r;
}
PushFrame& PushFrameAllocator::operator[](PFRef r) { return (PushFrame&)RegionAllocator<uint32_t>::operator[](r.x); }
PushFrame* PushFrameAllocator::lea       (PFRef r) { return (PushFrame*)RegionAllocator<uint32_t>::lea(r.x); }
PFRef      PushFrameAllocator::ael       (const PushFrame* t) { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); return { r }; }

void Theory::setSubstitutions(Map<PTRef,PtAsgn,PTRefHash>& substs) { getTSolverHandler().setSubstitutions(substs); }
vec<DedElem>& Theory::getDeductionVec()   { return deductions; }

TermMapper&  LRATheory::getTmap() { return tmap; }
LRALogic&    LRATheory::getLogic()    { return lralogic; }
LRATHandler& LRATheory::getTSolverHandler() { return lratshandler; }
LRATHandler* LRATheory::getTSolverHandler_new(vec<DedElem> &d) { return new LRATHandler(config, lralogic, d, tmap); }

TermMapper&  LIATheory::getTmap() { return tmap; }
LIALogic&    LIATheory::getLogic()    { return lialogic; }
LIATHandler& LIATheory::getTSolverHandler() { return liatshandler; }
LIATHandler* LIATheory::getTSolverHandler_new(vec<DedElem> &d) { return new LIATHandler(config, lialogic, d, tmap); }

