/*********************************************************************
 Author:
   Leonardo Alt <leonardoaltt@gmail.com>
 , Antti Hyvarinen <antti.hyvarinen@gmail.com>
 , Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT2 -- Copyright (C)   2012 - 2016, Antti Hyvarinen
                             2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include "LRASolver.h"
#include "LASolver.h"

#include "LA.h"

//#include "../liasolver/LIASolver.h"

static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");

/*
// MB: helper functions
namespace{
    bool isBoundSatisfied(Delta const & val, LABound const & bound ) {
        if (bound.getType() == bound_u){
            return val <= bound.getValue();
        }
        else {
            assert(bound.getType() == bound_l);
            return val >= bound.getValue();
        }
    }
}
*/
/*
bool LRASolver::isValid(PTRef tr)
{
    return logic.isNumConst(tr) || logic.isNumPlus(tr) || logic.isNumMinus(tr) || logic.isNumNeg(tr) ||
           logic.isNumTimes(tr) || logic.isNumDiv(tr) || logic.isNumEq(tr) || logic.isNumLeq(tr) || logic.isNumLt(tr) ||
           logic.isNumGeq(tr) || logic.isNumGt(tr) || logic.isNumVar(tr);
}

void LRASolver::isProperLeq(PTRef tr)
{
    assert(logic.isAtom(tr));
    assert(logic.isNumLeq(tr));
    Pterm& leq_t = logic.getPterm(tr);
    PTRef cons = leq_t[0];
    PTRef sum  = leq_t[1];
    assert(logic.isConstant(cons));
    assert(logic.isNumVar(sum) || logic.isNumPlus(sum) || logic.isNumTimes(sum));
    assert(!logic.isNumTimes(sum) || ((logic.isNumVar(logic.getPterm(sum)[0]) && (logic.mkNumNeg(logic.getPterm(sum)[1])) == logic.getTerm_NumOne()) ||
                                       (logic.isNumVar(logic.getPterm(sum)[1]) && (logic.mkNumNeg(logic.getPterm(sum)[0])) == logic.getTerm_NumOne())));
}*/


//opensmt::Real *
//LRASolver::newReal(const Real *old) {
//    Real * p_a = NULL;
//    if (!numbers_pool.empty())
//    {
//        p_a = numbers_pool.back( );
//        numbers_pool.pop_back( );
//        *p_a = *old;
//    }
//    else
//    {
//        p_a = new Real(*old);
//    }
//    return p_a;
//}



LRASolver::LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d)
    : logic(l)
//    , bindedRowsStore(l, lva, bra)
//    , pa(pta)
//    , polyStore(lva, pa, bindedRowsStore, l)
    , LASolver(descr_lra_solver, c, l, d)
    , delta(Delta::ZERO)
    //, bland_threshold(1000)
    //, lavarStore(lva, l)
    //, boundStore(ba, bla, lva, lavarStore, l)
    //, model(lva, boundStore, l)
{
    status = INIT;
}


void LRASolver::clearSolver()
{

    LASolver::clearSolver();
    delta = Delta::ZERO;
}

void LRASolver::computeConcreteModel(LVRef v) {
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
        concrete_model[lva[v].ID()] = new opensmt::Real(val.R() + val.D() * delta);
    }
    else {
        concrete_model[lva[v].ID()] = new opensmt::Real(model.read(v).R() + model.read(v).D() * delta);
    }
}

//
// Detect the appropriate value for symbolic delta and stores the model
//

void LRASolver::computeModel()
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
        if (model.read(v).D() == 0)
            continue; // If values are exact we do not need to consider them for delta computation

        assert( !isModelOutOfBounds(v) );

        Delta D;

        if (model.Lb(v).isMinusInf() || model.Ub(v).isPlusInf())
            D = Delta_PlusInf;
        else
            D = (model.Lb(v).R() + model.Ub(v).R())/2 - model.read(v).R();

        D = D/model.read(v).D();

        if (D < 0) D.negate();

        if (delta_abst > D)
            delta_abst = D;

/*
        curBound = Delta( Delta::ZERO );

        // Check if the lower bound can be used and at least one of delta and real parts are not 0
        const LABound& lbound = model.readLBound(v);
        const Delta& val_l = lbound.getValue();
        if (!val_l.isMinusInf()
            && (val_l.D() != 0 || model.read(v).D() != 0)
            && (val_l.R() != 0 || model.read(v).R() != 0))
        {
            curBound = lbound.getValue() - model.read(v);

            // if delta is > 0 then use delta for min
            if ( curBound.D() > 0 )
            {
                curDelta = -(curBound.R() / curBound.D());
                if ( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
                    minDelta = curDelta;
            }
            // if delta is < 0 than use delta for max
            else if  ( curBound.D() < 0 )
            {
                curDelta = -( curBound.R() / curBound.D() );
                if ( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
                    maxDelta = curDelta;
            }
        }
        const LABound& ubound = model.readUBound(v);
        const Delta&  val_u = ubound.getValue();
        if (!val_u.isPlusInf()
            && (val_u.D() != 0 || model.read(v).D() != 0)
            && (val_u.R() != 0 || model.read(v).R() != 0))
        {
            curBound = model.read(v) - ubound.getValue();

            // if delta is > 0 then use delta for min
            if ( curBound.D() > 0 )
            {
                curDelta = -(curBound.R() / curBound.D() );
                if ( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
                    minDelta = curDelta;
            }
            // if denominator is < 0 then use delta for max
            else if ( curBound.D() < 0 )
            {
                curDelta = -(curBound.R() / curBound.D());
                if ( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
                    maxDelta = curDelta;
            }
        }
*/
    }

    if (delta_abst.isPlusInf())
        delta = 1;
    else
        delta = delta_abst.R();

/*
    // TODO: check if it is it really true :)
    assert( minDelta >= 0 );
    assert( maxDelta <= 0 );
    delta = ( minDelta ) / 2;
*/

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
//
// The model system
//
bool LRASolver::isModelOutOfBounds(LVRef v) const
{
    return ( (model.read(v) > model.Ub(v)) || (model.read(v) < model.Lb(v)) );
}

bool LRASolver::isModelOutOfUpperBound(LVRef v) const
{
    return ( model.read(v)> model.Ub(v) );
}

bool LRASolver::isModelOutOfLowerBound(LVRef v) const
{
    return ( model.read(v) < model.Lb(v) );
}


const Delta LRASolver::overBound(LVRef v) const
{
    assert( isModelOutOfBounds(v) );
    if (isModelOutOfUpperBound(v))
    {
        return ( Delta(model.read(v) - model.Ub(v)) );
    }
    else if ( isModelOutOfLowerBound(v) )
    {
        return ( Delta(model.Lb(v) - model.read(v)) );
    }
    assert (false);
    printf("Problem in overBound, LRASolver.C:%d\n", __LINE__);
    exit(1);
}


bool LRASolver::isModelInteger(LVRef v) const
{
    return !( model.read(v).hasDelta() || !model.read(v).R().isInteger() );
}

bool LRASolver::isEquality(LVRef v) const
{
    return model.isEquality(v);
}

bool LRASolver::isUnbounded(LVRef v) const
{
    bool rval = model.isUnbounded(v);
//    if (rval)
//        printf("Var %s is unbounded\n", lva.printVar(v));
    return rval;
}
*/

// Given an inequality of the form c <= t(x_1, ..., x_n), set the bound
// for the expression on the right side.  If the inequality is of the
// form
//  (1) c <= x, set a lower bound for x
//  (2) c <= -x, set an upper bound for x
//  (3) c <= x1 + a2*x2 + ... + an*xn, set an upper bound for the slack
//      var x1 + a2*x2 + ... + an*xn
//  (4) c <= -x1 - a2*x2 - ... - an*xn, set a lower bound for the slack
//      var x1 + a2*x2 + ... + an*xn
//

/*
void LRASolver::setBound(PTRef leq_tr)
{
//    printf("Setting bound for %s\n", logic.printTerm(leq_tr));

    boundStore.addBound(leq_tr);
}
*/

//
// So far a temporary wrapper.  The idea is to avoid unnecessary delete & new.
//
//void LRASolver::getReal(Real*& r, PTRef cons)
//{
//    if (!numbers_pool.empty()) {
//        r = numbers_pool.back();
//        numbers_pool.pop_back();
//        *r = Real(logic.getRealConst(cons));
//    }
//    else {
//        r = new Real(logic.getRealConst(cons));
//    }
//}


Real LRASolver::getReal(PTRef r) {
    return logic.getNumConst(r);
}

/*
bool LRASolver::hasVar(PTRef expr) {
    expr =  logic.isNegated(expr) ? logic.mkNumNeg(expr) : expr;
    PTId id = logic.getPterm(expr).getId();
    return lavarStore.hasVar(id);
}

LVRef LRASolver::getLAVar_single(PTRef expr_in) {

    PTRef expr = logic.isNegated(expr_in) ? logic.mkNumNeg(expr_in) : expr_in;

    PTId id_pos = logic.getPterm(expr).getId();

    if (lavarStore.hasVar(id_pos))
        return lavarStore.getVarByPTId(id_pos);

    LVRef x = lavarStore.getNewVar(expr);
    return x;
}

Polynomial LRASolver::expressionToLVarPoly(PTRef term) {
    Polynomial poly;
    // If term is negated, we need to flip the signs of the poly
    bool negated = logic.isNegated(term);
    for (int i = 0; i < logic.getPterm(term).size(); i++) {
        PTRef v;
        PTRef c;
        logic.splitTermToVarAndConst(logic.getPterm(term)[i], v, c);
        LVRef var = getLAVar_single(v);
        tableau.nonbasicVar(var);
        Real coeff = getReal(c);

        if (negated) {
            coeff.negate();
        }
        poly.addTerm(var, std::move(coeff));
    }
    return poly;
}


//
// Get a possibly new LAVar for a PTRef term.  We may assume that the term is of one of the following forms,
// where x is a real variables and p_i are products of a real variable and a real constant
//
// (1) x
// (2a) (* x -1)
// (2b) (* -1 x)
// (3) x + p_1 + ... + p_n
// (4a) (* x -1) + p_1 + ... + p_n
// (4b) (* -1 x) + p_1 + ... + p_n
//
LVRef LRASolver::exprToLVar(PTRef expr) {
    LVRef x = LVRef_Undef;
    if (lavarStore.hasVar(expr)){
        x = lavarStore.getVarByPTId(logic.getPterm(expr).getId());
        if(isProcessedByTableau(x))
        { return x;}
    }

    if (logic.isNumVar(expr) || logic.isNumTimes(expr)) {
        // Case (1), (2a), and (2b)
        PTRef v;
        PTRef c;

        logic.splitTermToVarAndConst(expr, v, c);
        assert(logic.isNumVar(v) || (logic.isNegated(v) && logic.isNumVar(logic.mkNumNeg(v))));
        x = getLAVar_single(v);
        tableau.newNonbasicVar(x);
    }
    else {
        // Cases (3), (4a) and (4b)
        x= getLAVar_single(expr);
        tableau.newBasicVar(x, expressionToLVarPoly(expr));
    }
    assert(x != LVRef_Undef);
    return x;
}

//
// Reads the constraint into the solver
//
lbool LRASolver::declareTerm(PTRef leq_tr)
{
    if (!logic.isNumLeq(leq_tr)) return l_Undef;

    if (informed(leq_tr)) return l_Undef;

    informed_PTRefs.insert(leq_tr, true);


    if (status != INIT)
    {
        // Treat the PTRef as it is pushed on-the-fly
        //    status = INCREMENT;
        assert( status == SAT );
    }
    // DEBUG check
    isProperLeq(leq_tr);

    Pterm& t = logic.getPterm(leq_tr);

    while (known_preds.size() <= Idx(t.getId()))
        known_preds.push(false);
    known_preds[Idx(t.getId())] = true;

#if VERBOSE
    cerr << "; Informed of constraint " << logic.printTerm(tr_tr) << endl;
//    cout << this << endl;
#endif
    return l_Undef;
}
*/

//LVRef LRASolver::getBasicVarToFix() const {
//    int curr_var_id_x = max_var_id;
//    std::unordered_set<LVRef, LVRefHash> new_candidates;
//    for (auto it : candidates) {
//        assert(it != LVRef_Undef);
//        std::size_t current_poly_size = static_cast<std::size_t>(-1);
//        if (isModelOutOfBounds(it)) {
//            new_candidates.insert(it);
//            if (bland_rule) {
//                bland_counter++;
//                tsolver_stats.num_bland_ops++;
//                // Select the var with the smallest id
//                x = lva[it].ID() < curr_var_id_x ? it : x;
//                curr_var_id_x = lva[it].ID() < curr_var_id_x ? lva[it].ID() : curr_var_id_x;
//            } else { // Use heuristics that prefer short polynomials
//                pivot_counter++;
//                tsolver_stats.num_pivot_ops++;
//
//                if (x == LVRef_Undef || current_poly_size > tableau.getPolySize(it))
//                    x = it;
//            }
//        }
//    }
//    candidates.swap(new_candidates);
//}

/*
LVRef LRASolver::getBasicVarToFixByShortestPoly() const {
    std::unordered_set<LVRef, LVRefHash> new_candidates;
    LVRef current = LVRef_Undef;
    std::size_t current_poly_size = static_cast<std::size_t>(-1);
    for (auto it : candidates) {
        assert(it != LVRef_Undef);
        if (isModelOutOfBounds(it)) {
            new_candidates.insert(it);
            if (current == LVRef_Undef || current_poly_size > tableau.getPolySize(it)) {
                current = it;
                current_poly_size = tableau.getPolySize(it);

            }
        }
    }
    candidates.swap(new_candidates);
    return current;
}

LVRef LRASolver::getBasicVarToFixByBland() const {
    std::unordered_set<LVRef, LVRefHash> new_candidates;
    int curr_var_id_x = lavarStore.numVars();
    LVRef current = LVRef_Undef;
    for (auto it : candidates) {
        assert(it != LVRef_Undef);
        if (isModelOutOfBounds(it)) {
            new_candidates.insert(it);
                // Select the var with the smallest id
                current = lva[it].ID() < curr_var_id_x ? it : current;
                curr_var_id_x = lva[it].ID() < curr_var_id_x ? lva[it].ID() : curr_var_id_x;
            }
        }
    candidates.swap(new_candidates);
    return current;
}

LVRef LRASolver::findNonBasicForPivotByHeuristic(LVRef basicVar) {
    // favor more independent variables: those present in less rows
    assert(tableau.isBasic(basicVar));
    LVRef v_found = LVRef_Undef;
    if (model.read(basicVar) < model.Lb(basicVar)) {

        for (auto const &term : tableau.getPoly(basicVar)) {
            auto var = term.first;
            assert(tableau.isNonBasic(var));
            assert(var != basicVar);
            auto const &coeff = term.second;
            const bool is_coeff_pos = coeff > 0;

            if ((is_coeff_pos && model.read(var) < model.Ub(var)) ||
                (!is_coeff_pos && model.read(var) > model.Lb(var))) {
                if (v_found == LVRef_Undef) {
                    v_found = var;
                }
                    // heuristic favoring more independent vars
                else if (tableau.getColumn(v_found).size() > tableau.getColumn(var).size()) {
                    v_found = var;
                }
            }
        }
    }
    else if (model.read(basicVar) > model.Ub(basicVar)) {

        for (auto const &term : tableau.getPoly(basicVar)) {
            auto var = term.first;
            assert(tableau.isNonBasic(var));
            assert(var != basicVar);
            auto const &coeff = term.second;
            const bool is_coeff_pos = coeff > 0;

            if ((!is_coeff_pos && model.read(var) < model.Ub(var)) ||
                (is_coeff_pos && model.read(var) > model.Lb(var))) {
                if (v_found == LVRef_Undef) {
                    v_found = var;
                }
                    // heuristic favoring more independent vars
                else if (tableau.getColumn(v_found).size() > tableau.getColumn(var).size()) {
                    v_found = var;
                }
            }
        }
    }
    else{
        opensmt_error( "Error in bounds comparison" );
    }
    return v_found;
}

LVRef LRASolver::findNonBasicForPivotByBland(LVRef basicVar) {
    int max_var_id = lavarStore.numVars();
    LVRef y_found = LVRef_Undef;
    // Model doesn't fit the lower bound
    if (model.read(basicVar) < model.Lb(basicVar)) {
        // For the Bland rule
        int curr_var_id_y = max_var_id;
        // look for nonbasic terms to fix the breaking of the bound
        for (auto term : tableau.getPoly(basicVar)) {
            auto y = term.first;
            assert(basicVar != y);
            assert(tableau.isNonBasic(y));
            auto const &coeff = term.second;
            const bool coeff_is_pos = (coeff > 0);
            if ((coeff_is_pos && model.read(y) < model.Ub(y)) || (!coeff_is_pos && model.read(y) > model.Lb(y))) {
                // Choose the leftmost nonbasic variable with a negative (reduced) cost
                y_found = lva[y].ID() < curr_var_id_y ? y : y_found;
                curr_var_id_y = lva[y].ID() < curr_var_id_y ? lva[y].ID() : curr_var_id_y;
            }
        }
    }
    else if (model.read(basicVar) > model.Ub(basicVar)) {
        int curr_var_id_y = max_var_id;
        // look for nonbasic terms to fix the unbounding
        for (auto term : tableau.getPoly(basicVar)) {
            auto y = term.first;
            assert(basicVar != y);
            assert(tableau.isNonBasic(y));
            auto const &coeff = term.second;
            const bool &coeff_is_pos = (coeff > 0);
            if ((!coeff_is_pos && model.read(y) < model.Ub(y)) || (coeff_is_pos && model.read(y) > model.Lb(y))) {
                // Choose the leftmost nonbasic variable with a negative (reduced) cost
                y_found = lva[y].ID() < curr_var_id_y ? y : y_found;
                curr_var_id_y = lva[y].ID() < curr_var_id_y ? lva[y].ID() : curr_var_id_y;
            }
        }
    } else {
        opensmt_error("Error in bounds comparison");
    }
    return y_found;
}

*/

//
// Performs the main Check procedure to see if the current constraints
// and Tableau are satisfiable
//
bool LRASolver::check(bool complete) {

    return check_simplex(complete);

}

/*

bool LRASolver::check_simplex(bool complete) {
    // opensmt::StopWatch check_timer(tsolver_stats.simplex_timer);
//    printf(" - check %d\n", debug_check_count++);
    (void)complete;
    // check if we stop reading constraints
    if (status == INIT) {
        initSolver();
    }

    bool bland_rule = false;
    unsigned repeats = 0;
    unsigned pivot_counter = 0;
    unsigned bland_counter = 0;
    // These values are from Yices
    unsigned bthreshold = bland_threshold;
    if (nVars() > 10000)
        bthreshold *= 1000;
    else if (nVars() > 1000)
        bthreshold *= 100;

    // keep doing pivotAndUpdate until the SAT/UNSAT status is confirmed
    while (true) {
        repeats++;
        // clear the explanations vector
        explanation.clear( );
        explanationCoefficients.clear( );

        LVRef x = LVRef_Undef;

        if (!bland_rule && (repeats > tableau.getNumOfCols()))
            bland_rule = true;

        if(bland_rule){
            x = getBasicVarToFixByBland();
            ++bland_counter;
            ++tsolver_stats.num_bland_ops;
        }
        else{
            x = getBasicVarToFixByShortestPoly();
            ++pivot_counter;
            ++tsolver_stats.num_pivot_ops;
        }

        if (x == LVRef_Undef) {
            // If not found, check if problem refinement for integers is required
            //if (config.lra_integer_solver && complete)
                //return checkIntegersAndSplit( );

            // Otherwise - SAT
            refineBounds();
#ifdef GAUSSIAN_DEBUG
            computeModel();
#endif
//            cerr << "; USUAL SAT" << endl;
            setStatus(SAT);
            break;
//            return setStatus( SAT );
        }

        LVRef y_found = LVRef_Undef;
        if(bland_rule){
            y_found = findNonBasicForPivotByBland(x);
        }
        else{
            y_found = findNonBasicForPivotByHeuristic(x);
        }
        // if it was not found - UNSAT
        if (y_found == LVRef_Undef) {
            vec<PTRef> tmp;
            getConflictingBounds(x, tmp);
            for (int i = 0; i < tmp.size(); i++) {
                PTRef pure;
                lbool sgn;
                logic.purify(tmp[i], pure, sgn);
                explanation.push(PtAsgn(pure, sgn));
            }
            setStatus(UNSAT);
            break;
        }
        // if it was found - pivot old Basic x with non-basic y and do the model updates
        else {
            pivot(x, y_found);
        }
    }
    getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
//    printf(" - check ended\n");
//    printf(" => %s\n", getStatus() ? "sat" : "unsat");
//    if (getStatus())
//        model.printModelState();
    return getStatus();
}


//
// Push the constraint into the solver and increase the level
//
bool LRASolver::assertLit( PtAsgn asgn, bool reason )
{
    ( void )reason;

//    printf("Assert %d\n", debug_assert_count++);

    // Special cases of the "inequalitites"
    if (logic.isTrue(asgn.tr) && asgn.sgn == l_True) {
        tsolver_stats.sat_calls ++;
        return true;
    }
    if (logic.isFalse(asgn.tr) && asgn.sgn == l_False) {
        tsolver_stats.sat_calls ++;
        return true;
    }
    if (logic.isTrue(asgn.tr) && asgn.sgn == l_False) {
        tsolver_stats.unsat_calls ++;
        return false;
    }
    if (logic.isFalse(asgn.tr) && asgn.sgn == l_True) {
        tsolver_stats.unsat_calls ++;
        return false;
    }
    // check if we stop reading constraints
    if( status == INIT  )
        initSolver( );

    assert(asgn.sgn != l_Undef);

    bool is_reason = false;

    Pterm& t = logic.getPterm(asgn.tr);


    LABoundRefPair p = boundStore.getBoundRefPair(asgn.tr);
    LABoundRef bound_ref = asgn.sgn == l_False ? p.neg : p.pos;

//    printf("Model state\n");
//    model.printModelState();
//    printf("Asserting %s\n", boundStore.printBound(bound_ref));
//    printf(" - equal to %s%s\n", asgn.sgn == l_True ? "" : "not ", logic.pp(asgn.tr));

    LVRef it = lavarStore.getVarByLeqId(t.getId());
    // Constraint to push was not found in local storage. Most likely it was not read properly before
    assert(it != LVRef_Undef);
    assert(!isUnbounded(it));


    // skip if it was deduced by the solver itself with the same polarity
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].polarity == asgn.sgn && deduced[t.getVar()].deducedBy == id) {
        assert(getStatus());
        tsolver_stats.sat_calls ++;
        return getStatus();
    }
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].deducedBy == id) {
        is_reason = true; // This is a conflict!
    }

    if (assertBoundOnVar( it, bound_ref))
    {
        assert(getStatus());
        model.pushBound(bound_ref);
        assert(!is_reason);
        if (!is_reason) {
            setPolarity(asgn.tr, asgn.sgn);
            model.pushDecision(asgn);
            getSimpleDeductions(it, bound_ref);
            tsolver_stats.sat_calls++;
        }

    } else {
        tsolver_stats.unsat_calls++;
    }

    return getStatus();
}

bool LRASolver::assertBoundOnVar(LVRef it, LABoundRef itBound_ref)
{
    // No check whether the bounds are consistent for the polynomials.  This is done later with Simplex.

    assert( status == SAT );
    assert( it != LVRef_Undef );
    assert( !isUnbounded(it) );
    const LABound &itBound = ba[itBound_ref];

//  cerr << "; ASSERTING bound on " << *it << endl;

    // Check if simple SAT can be given
    if (model.boundSatisfied(it, itBound_ref))
        return getStatus();

    // Check if simple UNSAT can be given.  The last check checks that this is not actually about asserting equality.
    if (model.boundUnsatisfied(it, itBound_ref))
    {
        explanation.clear();
        explanationCoefficients.clear();

        if (itBound.getType() == bound_u)
        {
            PTRef tr = model.readLBound(it).getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.emplace_back( 1 );
        }
        else if (itBound.getType() == bound_l)
        {
            PTRef tr = model.readUBound(it).getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.emplace_back( 1 );
        }

        assert(itBound.getPTRef() != PTRef_Undef);
        explanation.push(itBound.getPtAsgn());
        explanationCoefficients.emplace_back(1);
        return setStatus( UNSAT );
    }

    // Update the Tableau data if a non-basic variable
    if (tableau.isNonBasic(it)) {
        if(!isBoundSatisfied(model.read(it), itBound)){
            changeValueBy(it, itBound.getValue() - model.read(it));
        }
        else{
//            std::cout << "Bound is satisfied by current assignment, no need to update model!\n\n";
        }
    }
    else // basic variable got a new bound, it becomes a possible candidate
    {
        if(!tableau.isActive(it)){
            throw "Not implemented yet!";
        }
        candidates.insert(it);
    }

//  LAVar *x = it;
//  cerr << "; ASSERTED bound on " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;

//  cerr  << "; NORMAL " << status <<endl;
    return getStatus();
}

//
// Push the solver one level down
//
void LRASolver::pushBacktrackPoint( )
{
    // Check if any updates need to be repeated after backtrack
    model.pushBacktrackPoint();
//    printf(" -> Push backtrack point.  Following is the state of the model after the push\n");
//    model.printModelState();

    // Update the generic deductions state
    TSolver::pushBacktrackPoint();
}

// Pop the solver one level up
// NOTE: this method should not be used, pop multiple points is more efficient with popBacktrackPoints rather than popping one by one
void LRASolver::popBacktrackPoint( ) {
    this->popBacktrackPoints(1);
}

// Pop the solver given number of times
//
void LRASolver::popBacktrackPoints(unsigned int count) {
    for ( ; count > 0; --count){
        PtAsgn dec = model.popBacktrackPoint();
        if (dec != PtAsgn_Undef) {
            clearPolarity(dec.tr);
        }
        TSolver::popBacktrackPoint();
    }
    assert(checkValueConsistency());
//    fixCandidates();
    assert(invariantHolds());
    setStatus(SAT);
}

void LRASolver::fixCandidates() {
    candidates.clear();
    for (const auto & row : tableau.getRows()) {
        candidates.insert(row.first);
    }
}

void LRASolver::pivot( const LVRef bv, const LVRef nv){
    assert(tableau.isBasic(bv));
    assert(tableau.isNonBasic(nv));
    assert(valueConsistent(bv));
//    tableau.print();
    updateValues(bv, nv);
    tableau.pivot(bv, nv);
//    tableau.print();
    assert(checkValueConsistency());
    assert(checkTableauConsistency());
}

void LRASolver::changeValueBy(LVRef var, const Delta & diff) {
    // update var's value
    model.write(var, model.read(var) + diff);
    candidates.insert(var);
    // update all (active) rows where var is present
    for( LVRef row : tableau.getColumn(var)){
        assert(tableau.isBasic(row));
        if(tableau.isActive(row)){
            model.write(row, model.read(row) + (tableau.getCoeff(row, var) * diff));
            candidates.insert(row);
        }
    }
}

void LRASolver::updateValues(const LVRef bv, const LVRef nv){
    assert(model.read(bv) < model.Lb(bv) || model.read(bv) > model.Ub(bv));
    auto bvNewVal = (model.read(bv) < model.Lb(bv)) ? model.Lb(bv) : model.Ub(bv);
    const auto & coeff = tableau.getCoeff(bv, nv);
    // nvDiff represents how much we need to change nv, so that bv gets to the right value
    auto nvDiff = (bvNewVal - model.read(bv)) / coeff;
    // update nv's value
    changeValueBy(nv, nvDiff);
}

//
// Perform all the required initialization after inform is complete
//
void LRASolver::initSolver()
{
    if (status == INIT)
    {
#ifdef GAUSSIAN_DEBUG
        cout << "Columns:" << '\n';
        for (int i = 0; i < columns.size(); i++)
            cout << columns[i] << '\n';
        cout << "Rows:" << '\n';
        for  (int i = 0; i < rows.size(); i++)
            cout << rows[i] << '\n';
#endif
        vec<PTRef> known_PTRefs;
        informed_PTRefs.getKeys(known_PTRefs);
        for(int i = 0; i < known_PTRefs.size(); ++i){
            PTRef leq_tr = known_PTRefs[i];
            Pterm& leq_t = logic.getPterm(leq_tr);

            // Terms are of form c <= t where
            //  - c is a constant and
            //  - t is either a variable or a sum
            PTRef cons = leq_t[0];
            PTRef term = leq_t[1];

            // Ensure that all variables exists, build the polynomial, and update the occurrences.
            LVRef v = exprToLVar(term);

            lavarStore.addLeqVar(leq_tr, v);

            // Assumes that the LRA variable has been already declared
            setBound(leq_tr);
        }
        boundStore.buildBounds(ptermToLABoundRefs); // Bounds are needed for gaussian elimination
        // Gaussian Elimination should not be performed in the Incremental mode!
        if (config.lra_gaussian_elim == 1 && config.do_substitutions())
            doGaussianElimination();

        model.initModel(lavarStore);

        fixCandidates();

        status = SAT;
    }
    else
        opensmt_error( "Solver can not be initialized in the state different from INIT" );
}

//
// Returns boolean value correspondent to the current solver status
//
inline bool LRASolver::getStatus( )
{
    switch( status ) {
        case SAT:
        {
            return true;
            break;
        }
        case UNSAT:
        {
            return false;
            break;
        }
        case INIT:
        case ERROR:
        default:
            opensmt_error( "Status is undef!" );
        return false;
    }
}

//
// Sets the new solver status and returns the correspondent lbool value
//
inline bool LRASolver::setStatus( LRASolverStatus s )
{
    status = s;
    if (s == UNSAT)
        has_explanation = true;
    return getStatus( );
}
*/

/*
//
// Returns the bounds conflicting with the actual model.
//
void LRASolver::getConflictingBounds( LVRef x, vec<PTRef> & dst )
{
    if (model.read(x) < model.Lb(x)) {
        // add all bounds for polynomial elements, which limit lower bound
        const LABound& b_f = model.readLBound(x);
        dst.push(b_f.getSign() == l_True ? b_f.getPTRef() : logic.mkNot(b_f.getPTRef()));
//        dst.push(model.readLBound(x).getPTRef());
//        dst.push(ba[bla[lva[x].getBounds()][lva[x].lbound()]].getPTRef());
        explanationCoefficients.emplace_back( 1 );
        for (auto const & term : tableau.getPoly(x)) {
            Real const & coeff = term.second;
            assert( ! coeff.isZero());
            auto const var = term.first;
            assert(var != x);
            if (coeff < 0) {
                const LABound& b = model.readLBound(var);
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );

                explanationCoefficients.push_back( -coeff );
            }
            else {
                const LABound& b = model.readUBound(var);
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );

                explanationCoefficients.push_back(coeff);
            }
        }

//        for (int i = 0; i < polyStore.getSize(lva[x].getPolyRef()); i++) {
//            const PolyTerm &pt = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)];
//            const Real &a = pt.coef;
//            assert( a != 0 );
//            LVRef y = pt.var;
//            //LVRef y = columns[lva[pt.var].getColId()];
//            assert(x != y);
//
//            if (a < 0) {
//                const LABound& b = model.readLBound(y);
////                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
//                assert( b.getPTRef() != PTRef_Undef );
//                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );
//
//                explanationCoefficients.push_back( -a );
//            }
//            else {
//                const LABound& b = model.readUBound(y);
////                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
//                assert( b.getPTRef() != PTRef_Undef );
//                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );
//
//                explanationCoefficients.push_back(a);
//            }
//        }
    }
    if (model.read(x) > model.Ub(x)) {
        // add all bounds for polynomial elements, which limit upper bound
//        dst.push(ba[bla[lva[x].getBounds()][lva[x].ubound()]].getPTRef());
        const LABound& b_f = model.readUBound(x);
        dst.push(b_f.getSign() == l_True ? b_f.getPTRef() : logic.mkNot(b_f.getPTRef()));
//        dst.push(model.readUBound(x).getPTRef());
        explanationCoefficients.emplace_back( 1 );

        for (auto const & term : tableau.getPoly(x)) {
            Real const & coeff = term.second;
            assert( ! coeff.isZero());
            auto const var = term.first;
            assert(var != x);
            if (coeff > 0) {
                const LABound& b = model.readLBound(var);
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );

                explanationCoefficients.push_back( coeff );
            }
            else {
                const LABound& b = model.readUBound(var);
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );

                explanationCoefficients.push_back(-coeff);
            }
        }
//        for (int i = 0; i < polyStore.getSize(lva[x].getPolyRef()); i++) {
//            const PolyTerm &pt = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)];
//            const Real &a = pt.coef;
//            assert( a != 0 );
//            LVRef y = pt.var;
//            //LVRef y = columns[lva[pt.var].getColId()];
//            assert(x != y);
//
//            if (a > 0) {
////                LABoundRef l_bound = bla[lva[y].getBounds()][lva[y].lbound()];
//                const LABound& b = model.readLBound(y);
////                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
//                assert( b.getPTRef() != PTRef_Undef );
//                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );
//                explanationCoefficients.push_back( a );
//            }
//            else {
////                LABoundRef u_bound = bla[lva[y].getBounds()][lva[y].ubound()];
//                const LABound& b = model.readUBound(y);
////                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
//
//                assert( b.getPTRef() != PTRef_Undef );
//                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );
//                explanationCoefficients.push_back(-a);
//            }
//        }
    }

//    printf("I now came up with an explanation.  It looks like this:\n");
//    for (int i = 0; i < dst.size(); i++)
//        printf("(%s) ", logic.printTerm(dst[i]));
//    printf("\n");

//    assert( dst.size() == polyStore.getSize(lva[x].getPolyRef())+1 ); // One for each term plus the broken equality

    ipartitions_t p = 1;
    p = ~p;
    p <<= 1;
    vec<PTRef> args_strong;
    vec<PTRef> args_weak;
    for(int i = 0; i < dst.size(); ++i)
    {
        if(isAstrict(logic.getIPartitions(dst[i]), p))
            args_strong.push(dst[i]);
        else if(isBstrict(logic.getIPartitions(dst[i]), p))
            args_weak.push(dst[i]);

        cerr << ";" << logic.printTerm(dst[i]);
        if(isAstrict(logic.getIPartitions(dst[i]), p))
            cerr << " is in A" << endl;
        else if(isBstrict(logic.getIPartitions(dst[i]), p))
            cerr << " is in B" << endl;
        else
            cerr << " is weird" << endl;
    }

    PTRef itp_strong = logic.mkAnd(args_strong);
    PTRef itp_weak = logic.mkNot(logic.mkAnd(args_weak));

    cerr << "; Strong itp:\n" << logic.printTerm(itp_strong) << endl;
    cerr << "; Weak itp:\n" << logic.printTerm(itp_weak) << endl;
  }*/


/*
void LRASolver::getSimpleDeductions(LVRef v, LABoundRef br)
{
//    printf("Deducing from bound %s\n", boundStore.printBound(br));
//    printf("The full bound list for %s:\n%s\n", logic.printTerm(lva[v].getPTRef()), boundStore.printBounds(v));

    LABound& bound = ba[br];
    if (bound.getValue().isInf())
        return;
    if (bound.getType() == bound_l) {
        for (int it = bound.getIdx() - 1; it >= 0; it = it - 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound &bound_prop = ba[bound_prop_ref];
            if (bound_prop.getValue().isInf())
                continue;
            if (bound_prop.getType() == bound_l) {
//                printf("Considering propagating %s\n", boundStore.printBound(bound_prop_ref));
                if (!hasPolarity(bound_prop.getPTRef())) {
                    if (deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_Undef) {
//                        printf(" => deduced %s (var %d)\n", boundStore.printBound(bound_prop_ref),
//                               logic.getPterm(bound_prop.getPTRef()).getVar());
                        lbool pol = bound_prop.getSign();
                        deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] = DedElem(id, pol); // id is the solver id
                        th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
                    } else {
//                        printf(" => but its deduced -value was %s instead of l_Undef\n", deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_True ? "l_True" : "l_False");
                    }
                }
                else {
//                    printf(" => but it already had a polarity\n");
                }
            }
        }
    }
    else if (bound.getType() == bound_u) {
        for (int it = bound.getIdx() + 1; it < boundStore.getBoundListSize(v) - 1; it = it + 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound &bound_prop = ba[bound_prop_ref];
            if (bound_prop.getValue().isInf())
                continue;
            if (bound_prop.getType() == bound_u) {
//                printf("Considering propagating %s\n", boundStore.printBound(bound_prop_ref));
                if (!hasPolarity(bound_prop.getPTRef())) {
                    if (deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_Undef) {
//                        printf(" => deduced %s\n", boundStore.printBound(bound_prop_ref));
                        lbool pol = bound_prop.getSign();
                        deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] = DedElem(id, pol);
                        th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
                    } else {
//                        printf(" => but its deduced -value was %s instead of l_Undef\n", deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_True ? "l_True" : "l_False");
                    }
                }
                else {
//                    printf(" => but it already had a polarity\n");
                }
            }
        }
    }
}

*/

/*
//
// Compute the current bounds for each row and tries to deduce something useful
//
void LRASolver::refineBounds( )
{

    // Check if polynomial deduction is enabled
    if (config.lra_poly_deduct_size == 0)
        return;
}

//
// Prints the current state of the solver (terms, bounds, tableau)
//
void LRASolver::print( ostream & out )
{
    model.printModelState();
    throw "Not implemented yet!";
    // print current non-basic variables
//    out << "Var:" << endl;
//    for ( unsigned i = 0; i < columns.size(); i++ )
//        out << logic.pp(lva[columns[i]].getPTRef()) << "\t";
//    out << endl;
//
//    // print the terms IDs
//    out << "Tableau:" << endl;
//    for ( unsigned i = 0; i < columns.size(); i++)
//        out << lva[columns[i]].ID() << "\t";
//    out << endl;
//
//    // print the Basic/Nonbasic status of terms
//    for ( unsigned i = 0; i < columns.size(); i++)
//        out << ( lva[columns[i]].isBasic() ? "B" : "N" ) << "\t";
//    out << endl;
//
//    // print the tableau cells (zeros are skipped)
//    // iterate over Tableau rows
//    for ( unsigned i = 0; i < rows.size( ); i++ ) {
//        auto const & row_poly = row_polynomials.at(rows[i]);
//        for (unsigned j = 0; j < columns.size(); j++) {
////            if (polyStore.has(lva[rows[i]].getPolyRef(), columns[j]))
////                out << pta[polyStore.find(lva[rows[i]].getPolyRef(), columns[j])].coef;
//            auto it = row_poly.find(columns[j]);
//            if (it != row_poly.end()){
//               out << it->second;
//            }
//            out << "\t";
//        }
//        out << endl;
//    }
}


void LRASolver::computeConcreteModel(LVRef v) {
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
        concrete_model[lva[v].ID()] = new opensmt::Real(val.R() + val.D() * delta);
    }
    else {
        concrete_model[lva[v].ID()] = new opensmt::Real(model.read(v).R() + model.read(v).D() * delta);
    }
}




void LRASolver::getConflict(bool, vec<PtAsgn>& e)
{
    for (int i = 0; i < explanation.size(); i++) {
        e.push(explanation[i]);

    }
//    printf(" => explanation: \n");
//    for (int i = 0; i < e.size(); i++) {
//        PtAsgn asgn = e[i];
//        LABoundRefPair p = boundStore.getBoundRefPair(asgn.tr);
//        LABoundRef bound_ref = asgn.sgn == l_False ? p.neg : p.pos;
//        printf("(%s) ", boundStore.printBound(bound_ref));
//    }
//    printf("\n");
//    vec<PTRef> check_me;
//    for (int i = 0; i < e.size(); i++) {
//        check_me.push(e[i].sgn == l_False ? logic.mkNot(e[i].tr) : e[i].tr);
//    }
////    printf("In PTRef this is %s\n", logic.pp(logic.mkAnd(check_me)));
//    assert(logic.implies(logic.mkAnd(check_me), logic.getTerm_false()));
}

 */

/*
//
// Detect the appropriate value for symbolic delta and stores the model
//
void LRASolver::computeModel()
{
    assert( status == SAT );

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
        if (model.read(v).D() == 0)
            continue; // If values are exact we do not need to consider them for delta computation

        assert( !isModelOutOfBounds(v) );

        Delta D;

        if (model.Lb(v).isMinusInf() || model.Ub(v).isPlusInf())
            D = Delta_PlusInf;
        else
            D = (model.Lb(v).R() + model.Ub(v).R())/2 - model.read(v).R();

        D = D/model.read(v).D();

        if (D < 0) D.negate();

        if (delta_abst > D)
            delta_abst = D;

    }


    if (delta_abst.isPlusInf())
        delta = 1;
    else
        delta = delta_abst.R();


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
*/


//
// Add the variable x with the coefficient p_v to the polynomial represented by
// s
//
//void LRASolver::addVarToRow( LVRef s, LVRef x, Real * p_v )
//{
//    assert(!lva[x].isBasic());
//    assert(lva[s].isBasic());
//
//    polyStore.add(lva[s].getPolyRef(), x, *p_v);
//}



/*
// We may assume that the term is of the following forms
// (1) (* x c)
// (2) (* c x)
// (3) c
opensmt::Real LRASolver::evaluateTerm(PTRef tr)
{
    Pterm& t = logic.getPterm(tr);
    opensmt::Real val(0);
    // Case (3)
    if (logic.isNumConst(tr))
        return logic.getRealConst(tr);

    // Cases (1) & (2)
    PTRef coef;
    PTRef var;
    logic.splitTermToVarAndConst(tr, var, coef);
    PTId id = logic.getPterm(var).getId();
    val += logic.getRealConst(coef) * *concrete_model[lva[lavarStore.getVarByPTId(id)].ID()];

    return val;
}

// We may assume that the term is of one of the following forms,
// where x is a real variables and p_i are products of a real variable and a real constant
//
// (1a) (* x -1)
// (1b) (* -1 x)
// (2) x + p_1 + ... + p_n
// (3a) (* x -1) + p_1 + ... + p_n
// (3b) (* -1 x) + p_1 + ... + p_n
//
ValPair LRASolver::getValue(PTRef tr) {
    if (!logic.hasSortNum(tr)) return ValPair_Undef;
    PTId id = logic.getPterm(tr).getId();
    opensmt::Real val(0);
    if (!lavarStore.hasVar(id)) {
        // This is a linear expression.
        if (logic.getPterm(tr).size() > 0) {
            Pterm &t = logic.getPterm(tr);
            for (int i = 0; i < t.size(); i++)
                val += evaluateTerm(t[i]);
        }
        else
            val = evaluateTerm(tr);
    }
    else
        val = *concrete_model[lva[lavarStore.getVarByPTId(id)].ID()];

    return ValPair(tr, val.get_str().c_str());
}

*/

//
// Destructor
//
LRASolver::~LRASolver( )
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

/*
//bool LRASolver::valueConsistent(LVRef v)
//{
//    const Delta& value = model.read(v);
//    Delta sum(0);
//    PolyRef pr = lva[v].getPolyRef();
////    printf("%s = ", value.printValue());
//    for (int i = 0; i < polyStore.getSize(pr); i++) {
//        const PolyTerm &t = pta[polyStore.readTerm(pr, i)];
//        Pterm& smt_term = logic.getPterm(lva[t.var].getPTRef());
//        sum += t.coef * model.read(t.var);
////        printf("+(%s*%s)", t.coef.get_str().c_str(), model.read(t.var).printValue());
//    }
////    printf(" = %s\n", sum.printValue());
//    assert(value == sum);
//    return value == sum;
//}

bool LRASolver::checkValueConsistency() const{
    bool res = true;
    for(auto row : tableau.getRows()) {
        if(tableau.isActive(row.first)){
            res &= valueConsistent(row.first);
        }
    }
    assert(res);
    return res;
}

bool LRASolver::valueConsistent(LVRef v) const
{
    const Delta& value = model.read(v);
//    std::cerr << "Value of " << v.x << " is: " << value.printValue() << '\n';
    Delta sum(0);
    for (auto & term : tableau.getPoly(v)){
//        std::cerr << "Value of " << term.first.x << " is: " << model.read(term.first).printValue() << '\n';
//        std::cerr << "Coeff of " << term.first.x << " is: " << term.second << '\n';
        sum += term.second * model.read(term.first);
    }
//    std::cerr << "Sum is: " << sum.printValue() << '\n';
//    printf(" = %s\n", sum.printValue());
    assert(value == sum);
    return value == sum;
}

//void LRASolver::crashInconsistency(LVRef v, int line) {
//    PolyRef pr = lva[v].getPolyRef();
//    printf("Var %s = %s is not consistent with its polynomial %s\n", lva.printVar(v), model.read(v).printValue(),
//           polyStore.printPoly(pr));
//    printf("At row %d, file LRASolver.C\n", line);
//    for (int i = 0; i < polyStore.getSize(pr); i++) {
//        const PolyTerm &t = pta[polyStore.readTerm(pr, i)];
//        printf(" %s * %s\n", t.coef.get_str().c_str(), model.read(t.var).printValue());
//    }
//    exit(10);
//}
//
// Check that the values of non-basic variables (columns) do not break asserted bounds
//
bool LRASolver::invariantHolds() const
{
    bool rval = true;
    for (auto var : tableau.getNonBasicVars()){
        assert(model.hasModel(var));
        if (isModelOutOfBounds(var)) {
//            auto & bounds = model.int_lbounds[lva[var].ID()];
//            for (int i = 0; i < bounds.size(); ++i){
//                auto & b = ba[bounds[i].br];
//                std::cout << "Bound with value: " << b.getValue().printValue() << " and level: " << bounds[i].dl << '\n';
//            }
//            auto & ubounds = model.int_ubounds[lva[var].ID()];
//            for (int i = 0; i < ubounds.size(); ++i){
//                auto & b = ba[ubounds[i].br];
//                std::cout << "Bound with value: " << b.getValue().printValue() << " and level: " << ubounds[i].dl << '\n';
//            }
//            auto & vals = model.int_model[lva[var].ID()];
//            for (int i = 0; i < vals.size(); ++i){
//                std::cout << "Eval with value: " << vals[i].d.printValue() << " and level: " << vals[i].dl << '\n';
//            }
            rval = false;
            printf("Non-basic (column) LRA var %s has value %s <= %s <= %s\n",
                   lva.printVar(var), model.Lb(var).printValue(),
                   model.read(var).printValue(), model.Ub(var).printValue());
            assert(false);
        }
    }
    return rval;
}
bool LRASolver::checkTableauConsistency() const {
    bool res = tableau.checkConsistency();
    assert(res);
    return res;
}

void LRASolver::doGaussianElimination( )
{
    auto eliminated = tableau.doGaussianElimination([this](LVRef v){return this->isUnbounded(v);});
    for(auto rit = eliminated.rbegin(); rit != eliminated.rend(); ++ rit) {
        auto entry = *rit;
        auto poly = entry.second;
        for(auto const & term : entry.second){
            auto var = term.first;
            auto it = removed_by_GaussianElimination.find(var);
            if( it != removed_by_GaussianElimination.end() && poly.contains(var)) {
                auto to_substitute = (*it).second;
                auto coeff = poly.getCoeff(var);
                poly.merge(to_substitute, coeff);
            }
        }
        removed_by_GaussianElimination.emplace(entry.first, poly);
    }
}*/

#ifdef PRODUCE_PROOF
//
// Compute interpolants for the conflict
//
PTRef
LRASolver::getInterpolant( const ipartitions_t & mask , map<PTRef, icolor_t> *labels)
{
    // Old implementation:
    //l = config.logic == QF_LRA || config.logic == QF_UFLRA
    //? QF_LRA
    //: QF_LIA;

    assert(status == UNSAT);
    assert (explanation.size()>1);

    if (verbose() > 1)
    {
        if (usingStrong())
            cerr << "; Using Strong for LRA interpolation" << endl;
        else if (usingWeak())
            cerr << "; Using Weak for LRA interpolation" << endl;
        else if(usingFactor())
            cerr << "; Using Factor " << getStrengthFactor() << " for LRA interpolation" << endl;
        else
            cerr << "; LRA interpolation algorithm unknown" << endl;
    }

    for(map<PTRef, icolor_t>::iterator it = labels->begin(); it != labels->end(); ++it)
    {
        //cout << "; PTRef " << logic.printTerm(it->first) << " has color " << it->second << endl;
    }

    LAExpression interpolant(logic);
    LAExpression interpolant_dual(logic);
    bool delta_flag = false;
    bool delta_flag_dual = false;

#ifdef ITP_DEBUG
    vec<PTRef> tr_vec;
    for (int i = 0; i < explanation.size(); i++)
    {
        PTRef tr_vecel = explanation[i].tr;
        tr_vec.push(explanation[i].sgn == l_False ? logic.mkNot(tr_vecel) : tr_vecel);
    }
    PTRef tr = logic.mkAnd(tr_vec);
    printf("; Explanation: \n");
    printf(";  %s\n", logic.printTerm(tr));
#endif

    for ( unsigned i = 0; i < explanation.size( ); i++ )
    {
        icolor_t color = I_UNDEF;
        const ipartitions_t & p = logic.getIPartitions(explanation[i].tr);
        Pterm& t = logic.getPterm(explanation[i].tr);

        if ( isAB( p, mask ) ) {
            color = I_AB;
        }
        else if ( isAlocal( p, mask ) ) {
            color = I_A;
        }
        else if ( isBlocal( p, mask ) ) {
            color = I_B;
        }
        if (color != I_A && color != I_AB && color != I_B)
        {
            printf("Error: color is not defined.\n");
            printf("  equation: %s\n", logic.printTerm(explanation[i].tr));
            printf("  mask: %s\n", mask.get_str().c_str());
            printf("  p: %s\n", p.get_str().c_str());
            assert(false);
        }
        assert( color == I_A
                || color == I_AB
                || color == I_B );

        //assert( usingStrong()
        //        || usingWeak()
        //        || usingRandom() );

        PTRef exp_pt = explanation[i].tr;
        if(labels != NULL && labels->find(exp_pt) != labels->end())
        {
            color = labels->find(exp_pt)->second;
            //cout << "; PTRef " << logic.printTerm(exp_pt) << " has Boolean color " << color << endl;
        }
        /*
        // McMillan algo: set AB as B
        else if ( usingStrong() && color == I_AB )
            color = I_B;
        // McMillan' algo: set AB as a
        else if ( usingWeak() && color == I_AB )
            color = I_A;
        // Pudlak algo: who cares
        else if ( usingRandom() && color == I_AB )
            color = rand() % 2 ? I_A : I_B;
        */

        //assert( color == I_A || color == I_B );

        // Add the conflict to the interpolant (multiplied by the coefficient)
        //if ((color == I_A && usingStrong()) || (color == I_B && usingWeak()))
        if(color == I_A || color == I_AB)
        {
            if (explanation[i].sgn == l_False)
            {
                interpolant.addExprWithCoeff(LAExpression(logic, explanation[i].tr), explanationCoefficients[i]);
                delta_flag=true;
            }
            else
            {
                interpolant.addExprWithCoeff(LAExpression(logic, explanation[i].tr), -explanationCoefficients[i]);
            }
        }
        //if ((color == I_A && usingStrong()) || (color == I_B && usingWeak()))
        if(color == I_B || color == I_AB)
        {
            if (explanation[i].sgn == l_False)
            {
                interpolant_dual.addExprWithCoeff(LAExpression(logic, explanation[i].tr), explanationCoefficients[i]);
                delta_flag_dual=true;
            }
            else
            {
                interpolant_dual.addExprWithCoeff(LAExpression(logic, explanation[i].tr), -explanationCoefficients[i]);
            }
        }
    }

    //cout << "; INTERPOLANT " << interpolant << endl;
    //cout << "; INTERPOLANT IS TRUE " << (interpolant.isTrue() ? "true" : "false") << endl;
    //cout << "; INTERPOLANT IS FALSE " << (interpolant.isFalse() ? "true" : "false") << endl;
    PTRef itp;
    if (interpolant.isTrue() && !delta_flag)
        itp = logic.getTerm_true();
    else if (interpolant.isFalse() || ( interpolant.isTrue() && delta_flag ))
        itp = logic.getTerm_false();
    else
    {
        vec<PTRef> args;
        if (usingFactor())
        {
            opensmt::Real const_strong = interpolant.getRealConstant();
            opensmt::Real const_weak = interpolant_dual.getRealConstant();
            PTRef nonconst_strong = interpolant.getPTRefNonConstant();
            PTRef nonconst_weak = interpolant_dual.getPTRefNonConstant();
            //cout << "; Constant Strong " << const_strong << endl;
            //cout << "; Constant Weak " << const_weak << endl;
            //cout << "; NonConstant Strong " << logic.printTerm(nonconst_strong) << endl;
            //cout << "; NonConstant Weak " << logic.printTerm(nonconst_weak) << endl;
            PTRef neg_strong = logic.mkRealNeg(nonconst_strong);
            //assert(neg_strong == nonconst_weak);

            opensmt::Real lower_bound = const_strong;
            opensmt::Real upper_bound = const_weak * -1;

            //cout << "; Lower bound is " << lower_bound << endl;
            //cout << "; Upper bound is " << upper_bound << endl;
            assert(upper_bound >= lower_bound);

            //cout << "; Strength factor from config is " << getStrengthFactor() << endl;
            opensmt::Real strength_factor(getStrengthFactor());
            if (strength_factor < 0 || strength_factor >= 1)
            {
                opensmt_error("LRA strength factor has to be in [0,1)");
            }
            opensmt::Real strength_diff = (upper_bound - lower_bound);
            //cout << "; Diff is " << strength_diff << endl;
            //cout << "; Factor is " << strength_factor << endl;
            opensmt::Real strength_delta = strength_diff * strength_factor;
            //cout << "; Delta is " << strength_delta << endl;
            opensmt::Real new_constant = lower_bound + (strength_diff * strength_factor);
            new_constant = new_constant * -1;
            //cout << "; New constant is " << new_constant << endl;
            args.push(logic.mkConst(new_constant));
            args.push(nonconst_strong);
        }
        else if (usingStrong())
        {
            args.push(logic.mkConst("0"));
            args.push(interpolant.toPTRef());
        }
        else if (usingWeak())
        {
            args.push(logic.mkConst("0"));
            args.push(interpolant_dual.toPTRef());
        }
        else
        {
            opensmt_error("Error: interpolation algorithm not set for LRA.");
        }

        char* msg;
        if (!usingWeak())
        {
            if (delta_flag)
                itp = logic.mkRealLt(args, &msg);
            else
                itp = logic.mkRealLeq(args, &msg);
        }
        else
        {
            if (delta_flag)
                itp = logic.mkRealLt(args, &msg);
            else
                itp = logic.mkRealLeq(args, &msg);
            itp = logic.mkNot(itp);
        }
    }

    if (verbose() > 1)
    {
        cerr << "; LRA Itp: " << logic.printTerm(itp) << endl;
    }

    return itp;
}

#endif

