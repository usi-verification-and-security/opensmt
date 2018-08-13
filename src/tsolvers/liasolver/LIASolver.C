#include "LIASolver.h"
#include "LASolver.h"



static SolverDescr descr_lia_solver("LIA Solver", "Solver for Quantifier Free Linear Integer Arithmetics");


TRes LIASolver::check( bool complete) {
    bool rval = check_simplex(complete);
    if (rval == true)
        return checkIntegersAndSplit();
    return rval ? TR_SAT : TR_UNSAT;
}

bool LIASolver::isModelInteger(LVRef v) const
{
    return !( model.read(v).hasDelta() || !model.read(v).R().isInteger() );
}

opensmt::Integer2 LIASolver::getInt(PTRef r) {
    return logic.getNumConst(r);
}

void LIASolver::clearSolver()
{

    LASolver::clearSolver();
    //delta = Delta::ZERO;
}

void LIASolver::computeConcreteModel(LVRef v) {
    while (concrete_model.size() <= lva[v].ID())
        concrete_model.push(nullptr);

    PTRef tr = lva[v].getPTRef();
    auto it = removed_by_GaussianElimination.find(v);
    if(it != removed_by_GaussianElimination.end()){
        auto const & representation = (*it).second;
        Delta val;
        for (auto const & term : representation) {
            val += term.second * model.read(term.first);
        }
        concrete_model[lva[v].ID()] = new opensmt::Real(val.R());
    }
    else {
        concrete_model[lva[v].ID()] = new opensmt::Real(model.read(v).R());
    }
}


//
// Detect the appropriate value for symbolic delta and stores the model
//

void LIASolver::computeModel()
{
    assert( status == SAT );
/*
    Real minDelta(0);
    Real maxDelta(0);
    Delta curDelta(0);
    Delta curBound(Delta::ZERO);
*/
    Delta delta_abst = Delta_PlusInf;  // We support plus infinity for this one.

    // Let x be a LV variable such that there are asserted bounds c_1 <= x and x <= c_2, where
    // (1) c_1 = (i1 | s1), c_2 = (i2 | -s2)
    // (2) s1, s2 \in {0, 1}
    // (3) val(x) = (R | D).
    // Then delta(x) := (i1+i2)/2 - R.
    // If x is not bounded from below or above, i.e., c_1 <= x, or x <= c_2, or neither, then
    // delta(x) := + Infty.
    // Now D at the same time is equal to k*\delta', and we need a value for \delta'.  So
    // \delta'(x) = D/k
    // Finally, \delta := min_{x \in LV |delta'(x)|}.

    for (unsigned i = 0; i < lavarStore.numVars(); ++i)
    {
        LVRef v = lavarStore.getVarByIdx(i);
        assert (model.read(v).D() == 0);

    }

#ifdef GAUSSIAN_DEBUG
    cerr << "; delta: " << curDelta << '\n';
#endif

    for ( unsigned i = 0; i < lavarStore.numVars(); i++)
    {
        LVRef v = lavarStore.getVarByIdx(i);
        computeConcreteModel(v);
    }
//    // Compute the value for each variable. Delta is taken into account
//    for ( unsigned i = 0; i < columns.size( ); ++i )
//        computeConcreteModel(columns[i], curDelta);
}

/*
Polynomial LIASolver::expressionToLVarPoly(PTRef term) {

    LASolver::expressionToLVarPoly(term);
    for (int i = 0; i < logic.getPterm(term).size(); i++) {
        int_vars.insert(var); //PS. maybe use insert with getVar?

    }
}*/

void LIASolver::notifyVar(LVRef v)
{
    if (!int_vars_map.has(v)) {
        int_vars_map.insert(v, true);
        int_vars.push(v);
    }

    while(cuts.size() <= lva[v].ID())
        cuts.push();
}

TRes LIASolver::checkIntegersAndSplit() {
    //assert(false);
    // assert( config.lra_integer_solver );
    //assert( removed_by_GaussianElimination.empty( ) );

    bool nonint_models = false;  // Keep track whether non-integer models are seen

    for (int i = 0; i < int_vars.size(); i++) {

        LVRef x = int_vars[i];
        if (removed_by_GaussianElimination.find(x) != removed_by_GaussianElimination.end()) {
            computeConcreteModel(x);
            model.write(x, Delta(*concrete_model[lva[x].ID()]));
        }
        if (!isModelInteger(x)) {
            nonint_models = true;
            //Prepare the variable to store a splitting value
            opensmt::Real c;

            // if val of int variable is not int, set it to integer by getting floor (c) and ceiling (c+1)
            // if real part of int var is int, then delta must be non-zero

            if (!model.read(x).R().isInteger()) {
                c = model.read(x).R().floor();
            } else { //but if the value from LRA solver returned is integer(which is here subset of real), then we consider delta part
                assert(model.read(x).D() != 0);
                if (model.read(x).D() < 0) {
                    c = model.read(x).R() - 1;
                } else {
                    c = model.read(x).R();
                }
            }

            // We might have this blocked already, and then the solver should essentially return "I don't know, please go ahead".
            if (cuts[lva[x].ID()].has(c)) {
                continue;
            }
            cuts[lva[x].ID()].insert(c, true);

            // Check if integer splitting is possible for the current variable
            if (c < model.Lb(x) && c + 1 > model.Ub(x)) { //then splitting not possible, and we create explanation

                explanation.push(model.readLBound(x).getPtAsgn());
                explanation.push(model.readUBound(x).getPtAsgn());
                //explanation = {model.readLBound(x).getPtAsgn(), model.readUBound(x).getPtAsgn()};
                setStatus(UNSAT);
                return TR_UNSAT;
            }



            //constructing new constraint
            //x <= c || x >= c+1;
            PTRef constr = logic.mkOr(logic.mkNumLeq(lva[x].getPTRef(), logic.mkConst(c)),
                       logic.mkNumGeq(lva[x].getPTRef(), logic.mkConst(c + 1)));
//            printf("LIA solver constraint %s\n", logic.pp(constr));

            splitondemand.push(constr);
            setStatus(NEWSPLIT);
            return TR_SAT;


            //what if more than one of the variables have fractional part? Shall we implement selection rule?
            //we also have to take care of not changing the values that already assigned to integers, here gomory cuts are important
            //branch and cut faster than branch and bound, so we need to add cut to the problem that cannot find int solution?

            //we need to add new constraints x <= c || x >= c+1 to problem constraints. Which vector stores problem constraints?
            //and ask LRASolver to check for them
            //what if LRA returns non int vals and again and again the process will be needed to be repeated
            //and we need to make sure it stops at some point
            //And will it go in depth first manner, or hybride?
            //if the model already integer we print stats SAT, else we continue on splitting until?(we need to stop) and print UNSAT
        }

    }
    if (nonint_models) {// We could not block these, so we tell the solver that we don't know the satisfiability.
        setStatus(UNKNOWN);
        return TR_UNKNOWN;
    }
    else {
        setStatus(SAT);
        return TR_SAT;
    }
}

void
LIASolver::getNewSplits(vec<PTRef>& splits)
{
    splitondemand.copyTo(splits);
    splitondemand.clear();
    setStatus(SAT);
}

LIASolver::LIASolver(SMTConfig & c, LIALogic& l, vec<DedElem>& d)
        : logic(l)
//    , bindedRowsStore(l, lva, bra)
//    , pa(pta)
//    , polyStore(lva, pa, bindedRowsStore, l)
        , LASolver(descr_lia_solver, c, l, d)

//, bland_threshold(1000)
//, lavarStore(lva, l)
//, boundStore(ba, bla, lva, lavarStore, l)
//, model(lva, boundStore, l)
{
    status = INIT;
}

LIASolver::~LIASolver( )
{
    lasolverstats.printStatistics(cerr);
    // Remove numbers
//    while( !numbers_pool.empty( ) )
//    {
//        assert( numbers_pool.back( ) );
//        delete numbers_pool.back( );
//        numbers_pool.pop_back( );
//    }
}

LIALogic&  LIASolver::getLogic()  { return logic; }