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

    Delta delta_abst = Delta_PlusInf;  // We support plus infinity for this one.

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
}

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
            //printf("LIA solver constraint %s\n", logic.pp(constr));

            splitondemand.push(constr);
            setStatus(NEWSPLIT);
            return TR_SAT;
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
        , LASolver(descr_lia_solver, c, l, d)

{
    status = INIT;
}

LIASolver::~LIASolver( )
{
    lasolverstats.printStatistics(cerr);

}

LIALogic&  LIASolver::getLogic()  { return logic; }