#include "LIASolver.h"
#include "LASolver.h"



static SolverDescr descr_lia_solver("LIA Solver", "Solver for Quantifier Free Linear Integer Arithmetics");


TRes LIASolver::check( bool complete) {
    bool rval = check_simplex(complete);
    if (complete && rval) {
        return checkIntegersAndSplit();
    }
    return rval ? TRes::SAT : TRes::UNSAT;
}

bool LIASolver::isModelInteger(LVRef v) const
{
    Delta val = simplex.getValuation(v);
    return !( val.hasDelta() || !val.R().isInteger() );
}

opensmt::Integer2 LIASolver::getInt(PTRef r) {
    return logic.getNumConst(r);
}

void LIASolver::clearSolver()
{

    LASolver::clearSolver();
    this->cuts.clear();
    this->int_vars.clear();
    this->int_vars_map.clear();
}

void LIASolver::notifyVar(LVRef v)
{
    if (!int_vars_map.has(v)) {
        int_vars_map.insert(v, true);
        int_vars.push(v);
    }

    while(static_cast<unsigned>(cuts.size()) <= getVarId(v))
        cuts.push();
}

TRes LIASolver::checkIntegersAndSplit() {

    bool nonint_models = false;  // Keep track whether non-integer models are seen

    for (int i = 0; i < int_vars.size(); i++) {

        LVRef x = int_vars[i];
        if (!isModelInteger(x)) {
            nonint_models = true;
            //Prepare the variable to store a splitting value
            opensmt::Real c;

            // if val of int variable is not int, set it to integer by getting floor (c) and ceiling (c+1)
            // if real part of int var is int, then delta must be non-zero
            Delta x_val = simplex.getValuation(x);
            if (!x_val.R().isInteger()) {
                c = x_val.R().floor();
            } else { //but if the value from LRA solver returned is integer(which is here subset of real), then we consider delta part
                assert(x_val.D() != 0);
                if (x_val.D() < 0) {
                    c = x_val.R() - 1;
                } else {
                    c = x_val.R();
                }
            }

            // We might have this blocked already, and then the solver should essentially return "I don't know, please go ahead".
            if (cuts[getVarId(x)].has(c)) {
                continue;
            }
            cuts[getVarId(x)].insert(c, true);

            // Check if integer splitting is possible for the current variable
            if (simplex.hasLBound(x) && simplex.hasUBound(x) && c < simplex.Lb(x) && c + 1 > simplex.Ub(x)) { //then splitting not possible, and we create explanation

                explanation.push(getAsgnByBound(simplex.readLBoundRef(x)));
                explanation.push(getAsgnByBound(simplex.readUBoundRef(x)));
                //explanation = {model.readLBound(x).getPtAsgn(), model.readUBound(x).getPtAsgn()};
                setStatus(UNSAT);
                return TRes::UNSAT;
            }

            //constructing new constraint
            //x <= c || x >= c+1;
            PTRef upperBound = logic.mkNumLeq(getVarPTRef(x), logic.mkConst(c));
            PTRef lowerBound = logic.mkNumGeq(getVarPTRef(x), logic.mkConst(c + 1));
            PTRef constr = logic.mkOr(upperBound, lowerBound);
            //printf("LIA solver constraint %s\n", logic.pp(constr));

            splitondemand.push(constr);
            setStatus(NEWSPLIT);
            return TRes::SAT;
        }

    }
    if (nonint_models) {// We could not block these, so we tell the solver that we don't know the satisfiability.
        setStatus(UNKNOWN);
        return TRes::UNKNOWN;
    }
    else {
        setStatus(SAT);
        return TRes::SAT;
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
        : LASolver(descr_lia_solver, c, l, d)
        , logic(l)

{
    status = INIT;
}

LIASolver::~LIASolver( )
{

}

LIALogic&  LIASolver::getLogic()  { return logic; }

/**
 * Given an imaginary inequality v ~ c (with ~ is either < or <=), compute the interger bounds on the variable
 *
 * @param c Real number representing the upper bound
 * @param strict inequality is LEQ if false, LT if true
 * @return The integer values of upper and lower bound corresponding to the inequality
 */
LABoundStore::BoundValuePair LIASolver::getBoundsValue(const Real & c, bool strict) {
    if (strict) {
        // v < c => UB is ceiling(c-1), LB is ceiling(c)
        return {Delta((c-1).ceil()), Delta(c.ceil())};
    }
    else {
        // v <= c => UB is floor(c), LB is floor(c+1)
        return {Delta(c.floor()), Delta((c+1).floor())};
    }
}
