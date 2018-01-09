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
#include "LAVar.h"
#include "Egraph.h"
#include "LA.h"

//#include "../liasolver/LIASolver.h"

static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");

bool LRASolver::isValid(PTRef tr)
{
    return logic.isRealConst(tr) || logic.isRealPlus(tr) || logic.isRealMinus(tr) || logic.isRealNeg(tr) ||
           logic.isRealTimes(tr) || logic.isRealDiv(tr) || logic.isRealEq(tr) || logic.isRealLeq(tr) || logic.isRealLt(tr) ||
           logic.isRealGeq(tr) || logic.isRealGt(tr) || logic.isRealVar(tr);
}

void LRASolver::isProperLeq(PTRef tr)
{
    assert(logic.isAtom(tr));
    assert(logic.isRealLeq(tr));
    Pterm& leq_t = logic.getPterm(tr);
    PTRef cons = leq_t[0];
    PTRef sum  = leq_t[1];
    assert(logic.isConstant(cons));
    assert(logic.isRealVar(sum) || logic.isRealPlus(sum) || logic.isRealTimes(sum));
    assert(!logic.isRealTimes(sum) || ((logic.isRealVar(logic.getPterm(sum)[0]) && (logic.mkRealNeg(logic.getPterm(sum)[1])) == logic.getTerm_RealOne()) ||
                                       (logic.isRealVar(logic.getPterm(sum)[1]) && (logic.mkRealNeg(logic.getPterm(sum)[0])) == logic.getTerm_RealOne())));
}
opensmt::Real *
LRASolver::newReal(const Real *old) {
    Real * p_a = NULL;
    if (!numbers_pool.empty())
    {
        p_a = numbers_pool.back( );
        numbers_pool.pop_back( );
        *p_a = *old;
    }
    else
    {
        p_a = new Real(*old);
    }
    return p_a;
}



LRASolver::LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d)
    : logic(l)
    , bindedRowsStore(l, lva, bra)
    , pa(pta)
    , polyStore(lva, pa, bindedRowsStore, l)
    , TSolver((SolverId)descr_lra_solver, (const char*)descr_lra_solver, c, d)
    , delta(Delta::ZERO)
    , bland_threshold(1000)
    , lavarStore(lva, l)
    , boundStore(ba, bla, lva, lavarStore, l)
    , model(lva, boundStore, l)
    , debug_check_count(0)
    , debug_assert_count(0)
{
    status = INIT;
    checks_history.push_back(0);
    first_update_after_backtrack = true;
}

void LRASolver::clearSolver()
{
    status = INIT;
    first_update_after_backtrack = true;
    explanationCoefficients.clear();
    columns.clear();
    rows.clear();
    checks_history.clear();
    checks_history.push_back(0);
    removed_by_GaussianElimination.clear();
    TSolver::clearSolver();

    lva.clear();
    pa.clear();
    ba.clear();

    lavarStore.clear();
}

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
}


bool LRASolver::isModelInteger(LVRef v) const
{
    return !( model.read(v).hasDelta() || !model.read(v).R().den_is_unit() );
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

void LRASolver::unbindRow(LVRef v, int row)
{
    assert(lva[v].isBasic() || lva[v].getBindedRowsRef() != OccListRef_Undef);
//    bindedRowStore.remove(v, row);
}


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
void LRASolver::setBound(PTRef leq_tr)
{
//    printf("Setting bound for %s\n", logic.printTerm(leq_tr));

    boundStore.addBound(leq_tr);
}

//
// So far a temporary wrapper.  The idea is to avoid unnecessary delete & new.
//
void LRASolver::getReal(Real*& r, PTRef cons)
{
    if (!numbers_pool.empty()) {
        r = numbers_pool.back();
        numbers_pool.pop_back();
        *r = Real(logic.getRealConst(cons));
    }
    else {
        r = new Real(logic.getRealConst(cons));
    }
}

bool LRASolver::hasVar(PTRef expr) {
    expr =  logic.isNegated(expr) ? logic.mkRealNeg(expr) : expr;
    PTId id = logic.getPterm(expr).getId();
    return lavarStore.hasVar(id);
}

LVRef LRASolver::getLAVar_single(PTRef expr_in) {
    PTRef expr = logic.isNegated(expr_in) ? logic.mkRealNeg(expr_in) : expr_in;
    LVRef x;

    PTId id_pos = logic.getPterm(expr).getId();
    PTId id_neg = logic.getPterm(logic.mkRealNeg(expr)).getId();
    int max_id = max(Idx(id_pos), Idx(id_neg));

    if (lavarStore.hasVar(id_pos))
        return lavarStore.getVarByPTId(id_pos);

    x = lavarStore.getNewVar(expr);

    vec<PolyTermRef> tmp;
    lva[x].setPolyRef(polyStore.makePoly(x, tmp));
    lva[x].setBindedRowsRef(bra.alloc());

    return x;
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
LVRef LRASolver::constructLAVarSystem(PTRef term) {
    LVRef x = LVRef_Undef;
    vec<PolyTermRef> sum_terms;
    if (lavarStore.hasVar(term))
        return lavarStore.getVarByPTId(logic.getPterm(term).getId());

    if (logic.isRealVar(term) || logic.isRealTimes(term)) {
        // Case (1), (2a), and (2b)
        PTRef v;
        PTRef c;
        logic.splitTermToVarAndConst(term, v, c);
        x = getLAVar_single(v);
        setNonbasic(x);
        if (lva[x].getColId() == -1) {
            lva[x].setColId(columns.size());
            columns.push(x);
        }
    }
    else {
        // Cases (3), (4a) and (4b)
        x = getLAVar_single(term);
        bool negated = logic.isNegated(term); // If term is negated, we need to flip the signs of the poly
        for (int i = 0; i < logic.getPterm(term).size(); i++) {
            PTRef v;
            PTRef c;
            logic.splitTermToVarAndConst(logic.getPterm(term)[i], v, c);
            LVRef nb = getLAVar_single(v);
            setNonbasic(nb);
            if (lva[nb].getColId() == -1) {
                lva[nb].setColId(columns.size());
                columns.push(nb);
            }
            Real* c_r;
            getReal(c_r, c);

            if (negated)
                c_r->negate();

            PolyTermRef ptr = pta.alloc(*c_r, nb);
            sum_terms.push(ptr);
        }
        setBasic(x);
        if (lva[x].getRowId() == -1) {
            lva[x].setRowId(rows.size());
            rows.push(x);
        }
        PolyRef pr  = polyStore.makePoly(x, sum_terms);
        lva[x].setPolyRef(pr);
    }
    return x;
}

void LRASolver::setBasic(LVRef x) {
    if (lva[x].isBasic())
        return;
    lva[x].setBasic();
}

void LRASolver::setNonbasic(LVRef x)
{
    if (!lva[x].isBasic())
        return;
    lva[x].setNonbasic();
}


//
// Reads the constraint into the solver
//
lbool LRASolver::declareTerm(PTRef leq_tr)
{
    if (informed(leq_tr)) return l_Undef;

    informed_PTRefs.insert(leq_tr, true);

    if (!logic.isRealLeq(leq_tr)) return l_Undef;


    if (status != INIT)
    {
        // Treat the PTRef as it is pushed on-the-fly
        //    status = INCREMENT;
        assert( status == SAT );
    }

    isProperLeq(leq_tr);


    Pterm& leq_t = logic.getPterm(leq_tr);

    // Terms are of form c <= t where
    //  - c is a constant and
    //  - t is either a variable or a sum
    PTRef cons = leq_t[0];
    PTRef term = leq_t[1];

    // Ensure that all variables exists, build the polynomial, and update the occurrences.
    LVRef v = constructLAVarSystem(term);

    lavarStore.addLeqVar(leq_tr, v);

    // Assumes that the LRA variable has been already declared
    setBound(leq_tr);

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

//
// Performs the main Check procedure to see if the current constraints
// and Tableau are satisfiable
//
bool LRASolver::check(bool complete)
{
    // opensmt::StopWatch check_timer(tsolver_stats.simplex_timer);
//    printf(" - check %d\n", debug_check_count++);
    (void)complete;
    // check if we stop reading constraints
    if (status == INIT)
        initSolver();

    LVRef x = LVRef_Undef;

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
    while (1) {
        repeats++;
        // clear the explanations vector
        explanation.clear( );
        explanationCoefficients.clear( );

        x = LVRef_Undef;

        if (!bland_rule && (repeats > columns.size()))
            bland_rule = true;

        // look for the basic x with the smallest index which doesn't fit the bounds
        // XXX Keep these in a heap, so that there's no need to go over all
        // of them every time!
        int max_var_id = lavarStore.numVars();
        int curr_var_id_x = max_var_id;
        for (int i = 0; i < rows.size(); i++) {
            LVRef it = rows[i];
            if (it == LVRef_Undef) continue; // There should not be nulls, since they result in quadratic slowdown?
            assert(valueConsistent(it));
            if (isModelOutOfBounds(it)) {
                if (bland_rule) {
                    bland_counter++;
                    tsolver_stats.num_bland_ops++;
                    // Select the var with the smallest id
                    x = lva[it].ID() < curr_var_id_x ? it : x;
                    curr_var_id_x = lva[it].ID() < curr_var_id_x ? lva[it].ID() : curr_var_id_x;
                } else { // Use heuristics that prefer short polynomials
                    pivot_counter++;
                    tsolver_stats.num_pivot_ops++;
                    if (x == LVRef_Undef || polyStore.getSize(lva[x].getPolyRef()) > polyStore.getSize(lva[it].getPolyRef()))
                        x = it;
                }
            }
        }

        if (x == LVRef_Undef) {
            // If not found, check if problem refinement for integers is required
            if (config.lra_integer_solver && complete)
                return checkIntegersAndSplit( );

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


        LVRef y = LVRef_Undef;
        LVRef y_found = y;

        // Model doesn't fit the lower bound
        if (model.read(x) < model.Lb(x)) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the breaking of the bound
            for (int i = 0; i < polyStore.getSize(polyStore.getPolyRef(x)); i++) {
                y = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)].var;
                assert(!lva[y].isBasic() );
                const opensmt::Real& a = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)].coef;
                if (x == y)
                    continue;

                const bool & a_is_pos = (a > 0);
                if ((a_is_pos && model.read(y) < model.Ub(y)) || (!a_is_pos && model.read(y) > model.Lb(y))) {
                    if (bland_rule) {
                        // Choose the leftmost nonbasic variable with a negative (reduced) cost
                        y_found = lva[y].ID() < curr_var_id_y ? y : y_found;
                        curr_var_id_y = lva[y].ID() < curr_var_id_y ? lva[y].ID() : curr_var_id_y;
                    } else {
                        if (y_found == LVRef_Undef)
                            y_found = y;
                        else if (getBindedRows(y_found).size() > getBindedRows(y).size()) // heuristic favoring more independent vars
                            y_found = y;
                    }
                }
            }

            // if it was not found - UNSAT
            if (y_found == LVRef_Undef) {
//                cerr << "; NO ways to SAT" << endl;
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
//                return setStatus(UNSAT);
            }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
            else {
                if (bland_rule)
                    printf("pivoting on x-id %d and y-id %d\n", curr_var_id_x, curr_var_id_y);
                pivotAndUpdate(x, y_found, model.Lb(x));
            }
        } else if (model.read(x) > model.Ub(x)) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the unbounding
            for (int i = 0; i < polyStore.getSize(polyStore.getPolyRef(x)); i++) {
                y = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)].var;
                if (x == y)
                    continue;
//                cerr << "; " << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                assert( !lva[y].isBasic() );
                const opensmt::Real& a = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)].coef;
                assert(a != 0);
                const bool & a_is_pos = (a > 0);
                if ((!a_is_pos && model.read(y) < model.Ub(y)) || (a_is_pos && model.read(y) > model.Lb(y))) {
                    if (bland_rule) {
                        y_found = lva[y].ID() < curr_var_id_y ? y : y_found;
                        curr_var_id_y = lva[y].ID() < curr_var_id_y ? lva[y].ID() : curr_var_id_y;
                    } else {
                        if (y_found == LVRef_Undef)
                            y_found = y;
                        else if (getBindedRows(y_found).size() > getBindedRows(y).size())
                            y_found = y;
                    }
                }
            }

            // if it was not found - UNSAT
            if (y_found == LVRef_Undef) {
//              cerr << "; NO ways to SAT 2" << endl;
                // add the x to explanations
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
                if (bland_rule)
                    printf("pivoting on x-id %d and y-id %d\n", curr_var_id_x, curr_var_id_y);
                pivotAndUpdate(x, y_found, model.Ub(x));
            }
        } else {
            opensmt_error( "Error in bounds comparison" );
        }
    }
    getStatus() == true ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
//    printf(" - check ended\n");
//    printf(" => %s\n", getStatus() ? "sat" : "unsat");
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

//  cerr << "; Pushing (" << ( pta.sgn == l_False ? "not " : "") << logic.printTerm(pta.tr)
//       << " - " << ptermToLavar[logic.getPterm(pta.tr).getId()] << endl;

    bool is_reason = false;

    Pterm& t = logic.getPterm(asgn.tr);


    LABoundRefPair p = boundStore.getBoundRefPair(asgn.tr);
    LABoundRef bound_ref = asgn.sgn == l_False ? p.neg : p.pos;

//    printf("Asserting %s\n", boundStore.printBound(bound_ref));
//    printf(" - equal to %s%s\n", asgn.sgn == l_True ? "" : "not ", logic.pp(asgn.tr));

    LVRef it = lavarStore.getVarByLeqId(t.getId());
    assert( !isUnbounded(it) );
    // Constraint to push was not found in local storage. Most likely it was not read properly before
    if ( it == LVRef_Undef ) {
        std::cout << logic.pp(asgn.tr) << "\n";
        throw "Unexpected push";
    }

    // skip if it was deduced by the solver itself with the same polarity
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].polarity == asgn.sgn && deduced[t.getVar()].deducedBy == id) {
        getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
//        printf(" => %s\n", getStatus() ? "sat" : "unsat");
        return getStatus();
    }
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].deducedBy == id) {
        is_reason = true; // This is a conflict!
    }
    setPolarity(asgn.tr, asgn.sgn);

    if (assertBoundOnVar( it, bound_ref))
    {
        model.pushBound(bound_ref);

        if (config.lra_theory_propagation == 1 && !is_reason)
            getSimpleDeductions(it, bound_ref);


        if (config.lra_check_on_assert != 0 && rand() % 100 < config.lra_check_on_assert)
        {
            // force solver to do check on assert with some probability
            return check( false );
        }
    }
    getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;

//    if (!getStatus())
//        printf(" => unsat\n");
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
//            PTRef tr = ba[bla[lva[it].getBounds()][lva[it].lbound()]].getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.push_back( Real( 1 ) );
        }
        else if (itBound.getType() == bound_l)
        {
            PTRef tr = model.readUBound(it).getPTRef();
//            PTRef tr = ba[bla[lva[it].getBounds()][lva[it].ubound()]].getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.push_back( Real( 1 ) );
        }

        assert(itBound.getPTRef() != PTRef_Undef);
        explanation.push(PtAsgn(itBound.getPTRef(), getPolarity(itBound.getPTRef())));
        explanationCoefficients.push_back( Real( 1 ) );
        return setStatus( UNSAT );
    }

    // Update the Tableau data if needed
    if (!lva[it].isBasic())
        update(it, itBound.getValue());

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
    // cerr << "; push " << pushed_constraints.size( ) << endl;
    // Check if any updates need to be repeated after backtrack
    model.pushBacktrackPoint();
//    printf(" -> Push backtrack point.  Following is the state of the model after the push\n");
//    model.printModelState();

//      cerr << "; re-apply " << pushed_constraints.size( ) << " - " << checks_history.back( ) << endl;

    // Update the generic deductions state
    TSolver::pushBacktrackPoint();
}

//
// Pop the solver one level up
//
void LRASolver::popBacktrackPoint( )
{
    model.popBacktrackPoint();
//    printf(" -> Pop backtrack point.  Following is the state of the model after the pop\n");
//    model.printModelState();
    first_update_after_backtrack = true;

    setStatus(SAT);
    TSolver::popBacktrackPoint();
}

// Remove row corresponding to pr.  Assumes that the variables appearing in the row have already updated their
// occurrence lists correspondingly.  Called only from gaussianElimination
void LRASolver::removeRow(PolyRef pr)
{
    int v_row = lva[pa[pr].getVar()].getRowId();
    // Replace basisRow slot with the last row in rows vector
    int m = rows.size() - 1;
    if (m > v_row) {
        assert(rows[m] != LVRef_Undef);
        rows[v_row] = rows[m];
        lva[rows[m]].setBasic();
        lva[rows[m]].setRowId(v_row);
    }
    lva[pa[pr].getVar()].setNonbasic();
    rows.pop();
}

void LRASolver::removeCol(LVRef v)
{
    int v_col = lva[v].getColId();
    if (v_col == -1)
        return; // Already removed
    assert(columns.size() > v_col);
    // Replace v_col slot with the last column in columns vector
    int m = columns.size() - 1;
    if (m > v_col) {
        lva[columns[m]].setColId(v_col);
        columns[v_col] = columns[m];
        lva[v].setColId(-1);
    }
    columns.pop();
}

void LRASolver::solveForVar(PolyRef pr, int idx, vec<PolyTermRef>& expr)
{
    LVRef x = pta[polyStore.readTerm(pr, idx)].var;
    Real x_coef_inverse = pta[polyStore.readTerm(pr, idx)].coef.inverse();
    Real x_coef_inverse_neg = -x_coef_inverse;
    expr.push(pta.alloc(x_coef_inverse, pa[pr].getVar()));
    for (int i = 0; i < polyStore.getSize(pr); i++) {
        if (i == idx) continue; // Skip x
        Real i_coef = pta[polyStore.readTerm(pr, i)].coef*x_coef_inverse_neg;
        expr.push(pta.alloc(i_coef, pta[polyStore.readTerm(pr, i)].var));
    }
//    printf("I derived the following expression for var %s: \n", lva.printVar(x));
//    for (int i = 0; i < expr.size(); i++)
//        printf(" %s", polyStore.printPolyTerm(expr[i]));
//    printf("\n");
}

//
// Look for unbounded terms and applies Gaussian elimination to them.
// Delete the column if succeeded
//

void LRASolver::doGaussianElimination( )
{
    vec<LVRef> elim_cols;

    for (unsigned i = 0; i < columns.size( ); ++i) {
        assert(columns[i] != LVRef_Undef);
        LVRef x = columns[i];
        assert(!lva[x].isBasic());
        if (!isUnbounded(x))
            continue;


        elim_cols.push(x);
        if (bra[lva[x].getBindedRowsRef()].size() == 0)
            continue;

//        printf("Var %s is unbounded and has more than zero occurrences in the polynomials\n", lva.printVar(x));
        // Derive an expression for x based on the first polynomial it appears
        BindedRow& row = bra[lva[x].getBindedRowsRef()][0];
        PolyRef basis = row.poly;
//        printf("First occurrence of var %s is the polynomial %s\n", lva.printVar(x), polyStore.printPoly(basis));

        vec<PolyTermRef> expr_for_x;
        int pos = row.pos;
        solveForVar(basis, pos, expr_for_x);

        vec<PolyRef> x_appearances;
        for (int j = 1; j < bra[lva[x].getBindedRowsRef()].size(); j++)
            x_appearances.push(bra[lva[x].getBindedRowsRef()][j].poly);

        for (int j = 0; j < x_appearances.size(); j++) {
            PolyRef pr = x_appearances[j];
            opensmt::Real x_coef = pta[polyStore.find(pr, x)].coef;
//            printf("Removing %s from the poly %s\n", lva.printVar(x), polyStore.printPoly(pr));
            polyStore.remove(x, pr);
//            printf("Resulted in %s\n", polyStore.printPoly(pr));
//            printf("Now making the substitution of %s on the poly %s\n", lva.printVar(x), polyStore.printPoly(pr));
            for (int k = 0; k < expr_for_x.size(); k++)
                polyStore.add(pr, pta[expr_for_x[k]].var, pta[expr_for_x[k]].coef * x_coef);
//            printf("Resulted in %s\n", polyStore.printPoly(pr));
        }

        // Clear removed row
        polyStore.remove(basis);

        // Keep polynomial in x to compute a model later
        const ModelPoly p(expr_for_x);
        removed_by_GaussianElimination.insert(lva[x].getPTRef(), p);

        removeRow(basis);

#ifdef GAUSSIAN_DEBUG
        printf("; Removed the row %s\n", logic.printTerm(LVA[basis].e));
        printf("; Removed column %s\n", logic.printTerm(LVA[x].e));
        printf("; rows: %d, columns: %d\n", rows.size(), nVars());
#endif
    }

    for (int i = 0; i < elim_cols.size(); i++)
        removeCol(elim_cols[i]);
}


//
// updates the model values according to asserted bound
//
void LRASolver::update( LVRef x, const Delta & v )
{
    // update model value for all basic terms
    const Delta x_delta = v - model.read(x);
    model.write(x, v);
    for (int i = 0; i < bra[lva[x].getBindedRowsRef()].size(); i++) {
        BindedRow& el = bra[lva[x].getBindedRowsRef()][i];
        LVRef row = pa[el.poly].getVar();
        int pos   = el.pos;
        Delta increment(pta[polyStore.readTerm(lva[row].getPolyRef(), pos)].coef * x_delta);
        model.write(row, model.read(row) + increment);

        //TODO: make a separate config value for suggestions
        //TODO: sort the order of suggestion requesting based on metric (Model increase, out-of-bound distance etc)
        //    if( config.lra_theory_propagation == 3 )
        //    {
        //      if( suggestions.empty( ) )
        //        rows[it->key]->getSuggestions( suggestions, id );
        //    }
        assert(valueConsistent(row));
    }
//  cerr << "; UPDATED nonbasic " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;
}

//
// pivots x and y in solver and does all updates
//
void LRASolver::pivotAndUpdate( LVRef bv, LVRef nv, const Delta & v )
{
//  std::cerr << "; PIVOT AND UPDATE" << *bv << " - " << *nb << " - " << v << endl;
    assert( bv != nv );
    assert( lva[bv].isBasic() );
    assert( !lva[nv].isBasic() );

    assert( polyStore.has(lva[bv].getPolyRef(), nv) );

    // get Theta (zero if Aij is zero)
    const Real& a = pta[polyStore.find(lva[bv].getPolyRef(), nv)].coef;

    Delta theta(( v - model.read(bv) ) / a);

    // update models of nb and bv
    model.write(bv, v);
    model.write(nv, model.read(nv)+theta);

    int nv_pos = -1; // nv's position in bv's polynomial
    // update model of Basic variables
    for (int i = 0; i < bra[lva[nv].getBindedRowsRef()].size(); i++) {
        LVRef bv_other = pa[bra[lva[nv].getBindedRowsRef()][i].poly].getVar();
        int pos = bra[lva[nv].getBindedRowsRef()][i].pos;
        if (bv_other != bv) {
            model.write(bv_other, model.read(bv_other)+pta[polyStore.readTerm(lva[bv_other].getPolyRef(), pos)].coef * theta);
        }
        else {
            nv_pos = pos;
        }
    }
    assert(nv_pos != -1);

    // pivoting bv and bv

#if FAST_RATIONALS
    const Real inverse = -FastRational_inverse( a );
#else
    const Real inverse = -1 / a;
#endif
    const Real neg_inverse = -inverse;

    PolyTermRef nv_term; // The term containing nv will be stored here
    // Solve for nv
    PolyRef pr = lva[bv].getPolyRef();
    for (int i = 0; i < polyStore.getSize(pr); i++) {
        PolyTermRef ptr = polyStore.readTerm(pr, i);
        if (pta[ptr].var == nv)
            nv_term = ptr;
        else {
            polyStore.updateCoef(ptr, pta[ptr].coef*inverse);
        }
    }
    polyStore.updateVar(pr, nv);
    polyStore.updateTerm(pr, nv_term, bv, neg_inverse);

    // pr is now the new polynomial for nv
    lva[nv].setPolyRef(pr);
    lva[bv].setPolyRef(PolyRef_Undef);


    // We will add bv to basic vectors so it needs to be set non-basic
    lva[bv].setNonbasic();
    // now change the attribute values for all rows where nv was present
    while (bra[lva[nv].getBindedRowsRef()].size() != 0) {
        PolyRef row = bra[lva[nv].getBindedRowsRef()][0].poly;
        int     pos = bra[lva[nv].getBindedRowsRef()][0].pos;
        assert( pta[polyStore.readTerm(row, pos)].coef != 0 );

        // copy a to the new Real variable (use memory pool)

        const Real& a = *newReal(&pta[polyStore.readTerm(row, pos)].coef);

        // Remove first nv from the poly.
        polyStore.remove(nv, row);
        // P_i = P_i + a_nv * P_bv (iterate over all elements of P_bv)
        for (int j = 0; j < polyStore.getSize(pr); j++) {
            LVRef col = pta[polyStore.readTerm(pr, j)].var;
            const Real &b = pta[polyStore.readTerm(pr, j)].coef;

            Real tmp = a*b;
            Real* p_c = newReal(&tmp);


            // Add the variable col with factor p_c to row's polynomial
            polyStore.add(row, col, *p_c);
            // It could be that the poly changed so we need to update our local reference row accordingly
            row = lva[pa[row].getVar()].getPolyRef();
        }
    }
    // nv will become the new basic var, so we need to remove its occurrences
    BindedRows& b = bindedRowsStore.getBindedRows(nv);
    b.clear();

    // swap x and y (basicID, polynomial, bindings)
    lva[bv].setPolyRef(PolyRef_Undef);
    int row_id = lva[bv].getRowId();
    lva[nv].setRowId(row_id);
    assert(rows[row_id] == bv);
    // Remove bv from rows, add nv to rows.
    rows[row_id] = nv;
    lva[bv].setNonbasic();
    lva[nv].setBasic();
    assert( polyStore.has(pr, bv) );

    assert( lva[bv].getPolyRef() == PolyRef_Undef );
    assert( polyStore.getSize(lva[nv].getPolyRef()) > 0 );
    assert( bra[lva[bv].getBindedRowsRef()].size() > 0 );
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
        boundStore.buildBounds(ptermToLABoundRefs); // Bounds are needed for gaussian elimination
        // Gaussian Elimination should not be performed in the Incremental mode!
        if (config.lra_gaussian_elim == 1 && config.do_substitutions())
            doGaussianElimination();

        model.initModel(lavarStore);

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
        explanationCoefficients.push_back( Real( 1 ) );
        for (int i = 0; i < polyStore.getSize(lva[x].getPolyRef()); i++) {
            const PolyTerm &pt = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)];
            const Real &a = pt.coef;
            assert( a != 0 );
            LVRef y = pt.var;
            //LVRef y = columns[lva[pt.var].getColId()];
            assert(x != y);

            if (a < 0) {
                const LABound& b = model.readLBound(y);
//                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );

                explanationCoefficients.push_back( -a );
            }
            else {
                const LABound& b = model.readUBound(y);
//                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );

                explanationCoefficients.push_back(a);
            }
        }
    }
    if (model.read(x) > model.Ub(x)) {
        // add all bounds for polynomial elements, which limit upper bound
//        dst.push(ba[bla[lva[x].getBounds()][lva[x].ubound()]].getPTRef());
        const LABound& b_f = model.readUBound(x);
        dst.push(b_f.getSign() == l_True ? b_f.getPTRef() : logic.mkNot(b_f.getPTRef()));
//        dst.push(model.readUBound(x).getPTRef());
        explanationCoefficients.push_back( Real( 1 ) );

        for (int i = 0; i < polyStore.getSize(lva[x].getPolyRef()); i++) {
            const PolyTerm &pt = pta[polyStore.readTerm(polyStore.getPolyRef(x), i)];
            const Real &a = pt.coef;
            assert( a != 0 );
            LVRef y = pt.var;
            //LVRef y = columns[lva[pt.var].getColId()];
            assert(x != y);

            if (a > 0) {
//                LABoundRef l_bound = bla[lva[y].getBounds()][lva[y].lbound()];
                const LABound& b = model.readLBound(y);
//                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");
                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );
                explanationCoefficients.push_back( a );
            }
            else {
//                LABoundRef u_bound = bla[lva[y].getBounds()][lva[y].ubound()];
                const LABound& b = model.readUBound(y);
//                printf("The bound is %s\n", b.getSign() == l_True ? "positive" : "negative");

                assert( b.getPTRef() != PTRef_Undef );
                dst.push( b.getSign() == l_True ? b.getPTRef() : logic.mkNot(b.getPTRef()) );
                explanationCoefficients.push_back(-a);
            }
        }
    }

//    printf("I now came up with an explanation.  It looks like this:\n");
//    for (int i = 0; i < dst.size(); i++)
//        printf("(%s) ", logic.printTerm(dst[i]));
//    printf("\n");

    assert( dst.size() == polyStore.getSize(lva[x].getPolyRef())+1 ); // One for each term plus the broken equality

/*
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
  */
}

void LRASolver::getSimpleDeductions(LVRef v, LABoundRef br)
{
//    printf("Deducing from bound %s\n", boundStore.printBound(br));
//    printf("The full bound list for %s:\n", logic.printTerm(lva[v].getPTRef()));
//    for (BoundIndex it = BoundIndex(0); it < BoundIndex(bound_list.size()); it=it+1)
//        printf("  %s (var %d)\n", boundStore.printBound(bound_list[it]), logic.getPterm(ba[bound_list[it]].getPTRef()).getVar());

    LABound& bound = ba[br];
    if (bound.getValue().isInf())
        return;
    if (bound.getType() == bound_l) {
        for (int it = bound.getIdx() - 1; it >= 0; it = it - 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound& bound_prop = ba[bound_prop_ref];
            if (bound_prop.getValue().isInf())
                continue;
            if ((bound_prop.getType() == bound_l) &&
                !hasPolarity(bound_prop.getPTRef()) &&
                deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_Undef)
            {
//                printf(" => deduced %s (var %d)\n", boundStore.printBound(bound_prop_ref), logic.getPterm(bound_prop.getPTRef()).getVar());
                lbool pol = bound_prop.getSign();
                deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] = DedElem(id, pol); // id is the solver id
                th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
            }
        }
    }
    else if (bound.getType() == bound_u) {
        for (int it = bound.getIdx() + 1; it < boundStore.getBoundListSize(v)-1; it = it + 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound& bound_prop = ba[bound_prop_ref];
            if (bound_prop.getValue().isInf())
                continue;
            if ((bound_prop.getType() == bound_u) &&
                !hasPolarity(bound_prop.getPTRef()) &&
                (deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_Undef))
            {
//                printf(" => deduced %s\n", boundStore.printBound(bound_prop_ref));
                lbool pol = bound_prop.getSign();
                deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] = DedElem(id, pol);
                th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
            }
        }
    }
}

//
// Compute the current bounds for each row and tries to deduce something useful
//
void LRASolver::refineBounds( )
{

    // Check if polynomial deduction is enabled
    if (config.lra_poly_deduct_size == 0)
        return;
    // Fix this if necessary
/*
    // iterate over all rows affected in the current check
    for (set<LAVar *>::const_iterator t_it = touched_rows.begin( ); t_it != touched_rows.end( ); ++t_it)
  {
    assert( ( *t_it )->isBasic( ) );
    LAVar * row = *t_it;

    bool UpInf = false; // become true when polynomial is infinite on the upper bound
    bool LoInf = false; // become true when polynomial is infinite on the lower bound
    bool UpExists = false; // flag is used to track if Up was initialized
    bool LoExists = false; // flag is used to track if Lo was initialized
    Delta Up( Delta::ZERO ); // upper bound value
    Delta Lo( Delta::ZERO ); // lower bound value
    int UpInfID = -1; // used to track the ID of the only element with infinite upper bound
    int LoInfID = -1; // used to track the ID of the only element with infinite lower bound

    // summarize all bounds for the polynomial
    for( LARow::iterator it = row->polynomial.begin( ); it != row->polynomial.end( ); row->polynomial.getNext( it ) )
    {
      Real & a = ( *( it->coef ) );
      LAVar * col = columns[it->key];

      assert( a != 0 );
      bool a_lt_zero = a < 0;

      // check if the upper (lower) bound is infinite or can be added to the summarized value of the upper bound
      if( !UpInf && ( ( col->U( ).isPlusInf( ) && !a_lt_zero ) || ( col->L( ).isMinusInf( ) && a_lt_zero ) ) )
      {
        if( UpInfID == -1 )
          UpInfID = col->ID( ); // one element can be unbounded
        else
          UpInf = true; // no upper bound exists
      }
      else if( !UpInf )
      {
        // add lower or upper bound (depending on the sign of a_i)
        if( UpExists )
          Up += a * ( a_lt_zero ? col->L( ) : col->U( ) );
        else
        {
          Up = a * ( a_lt_zero ? col->L( ) : col->U( ) );
          UpExists = true;
        }
      }

      // check if the lower (upper) bound is infinite or can be added to the summarized value of the lower bound
      if( !LoInf && ( ( col->U( ).isPlusInf( ) && a_lt_zero ) || ( col->L( ).isMinusInf( ) && !a_lt_zero ) ) )
      {
        if( LoInfID == -1 ) // one element can be unbounded
          LoInfID = col->ID( );
        else
          LoInf = true; // no lower bound exists
      }
      else if( !LoInf )
      {
        // add lower or upper bound (depending on the sign of a_i)
        if( LoExists )
          Lo += a * ( !a_lt_zero ? col->L( ) : col->U( ) );
        else
        {
          Lo = a * ( !a_lt_zero ? col->L( ) : col->U( ) );
          LoExists = true;
        }
      }

      // stop if both lower or upper bounds become infinite
      if( UpInf && LoInf )
        break;
    }

    // check if the computed values are logically correct
    //    if( UpExists && LoExists && !UpInf && !LoInf && UpInfID == LoInfID )
    //      assert( Up >= Lo );

    // deduct from upper bound (if exists)
    if( !UpInf && UpExists )
    {
      // first check if one element is currently unbounded
      if( UpInfID != -1 )
      {
        LAVar * col = columns[UpInfID];
        const Real & a = ( *( row->polynomial.find( UpInfID )->coef ) );
        assert( a != 0 );
        const Delta & b = -1 * Up / a;
        bool a_lt_zero = a < 0;

        if( a_lt_zero && col->U( ) > b )
          col->getDeducedBounds( b, bound_u, th_deductions, id );
        else if( !a_lt_zero && col->L( ) < b )
          col->getDeducedBounds( b, bound_l, th_deductions, id );
      }
      // if all are bounded then try to deduce for all of them
      else
      {
        for( LARow::iterator it = row->polynomial.begin( ); it != row->polynomial.end( ); row->polynomial.getNext( it ) )
        {
          const Real & a = ( *( it->coef ) );
          assert( a != 0 );
          LAVar * col = columns[it->key];
          bool a_lt_zero = a < 0;
          const Delta & b = ( a * ( a_lt_zero ? col->L( ) : col->U( ) ) - Up ) / a;

          if( a_lt_zero && col->U( ) >= b )
            col->getDeducedBounds( b, bound_u, th_deductions, id );
          else if( !a_lt_zero && col->L( ) <= b )
            col->getDeducedBounds( b, bound_l, th_deductions, id );
        }
      }
    }

    // deduct from lower bound (if exists)
    if( !LoInf && LoExists )
    {
      // first check if one element is currently unbounded
      if( LoInfID != -1 )
      {
        LAVar * col = columns[LoInfID];
        const Real & a = ( *( row->polynomial.find( LoInfID )->coef ) );
        assert( a != 0 );
        const Delta & b = -1 * Lo / a;
        bool a_lt_zero = a < 0;

        if( !a_lt_zero && col->U( ) > b )
          col->getDeducedBounds( b, bound_u, th_deductions, id );
        else if( a_lt_zero && col->L( ) < b )
          col->getDeducedBounds( b, bound_l, th_deductions, id );
      }
      // if all are bounded then try to deduce for all of them
      else
      {
        for( LARow::iterator it = row->polynomial.begin( ); it != row->polynomial.end( ); row->polynomial.getNext( it ) )
        {
          const Real & a = ( *( it->coef ) );
          assert( a != 0 );
          LAVar * col = columns[it->key];
          bool a_lt_zero = a < 0;
          const Delta & b = ( a * ( !a_lt_zero ? col->L( ) : col->U( ) ) - Lo ) / a;

          if( !a_lt_zero && col->U( ) >= b )
            col->getDeducedBounds( b, bound_u, th_deductions, id );
          else if( a_lt_zero && col->L( ) <= b )
            col->getDeducedBounds( b, bound_l, th_deductions, id );
        }
      }
    }
  }
  touched_rows.clear( );
*/
}

//
// Prints the current state of the solver (terms, bounds, tableau)
//
void LRASolver::print( ostream & out )
{
    model.printModelState();

    // print current non-basic variables
    out << "Var:" << endl;
    for ( unsigned i = 0; i < columns.size(); i++ )
        out << logic.pp(lva[columns[i]].getPTRef()) << "\t";
    out << endl;

    // print the terms IDs
    out << "Tableau:" << endl;
    for ( unsigned i = 0; i < columns.size(); i++)
        out << lva[columns[i]].ID() << "\t";
    out << endl;

    // print the Basic/Nonbasic status of terms
    for ( unsigned i = 0; i < columns.size(); i++)
        out << ( lva[columns[i]].isBasic() ? "B" : "N" ) << "\t";
    out << endl;

    // print the tableau cells (zeros are skipped)
    // iterate over Tableau rows
    for ( unsigned i = 0; i < rows.size( ); i++ ) {
        for (unsigned j = 0; j < columns.size(); j++) {
            if (polyStore.has(lva[rows[i]].getPolyRef(), columns[j]))
                out << pta[polyStore.find(lva[rows[i]].getPolyRef(), columns[j])].coef;
            out << "\t";
        }
        out << endl;
    }
}


void LRASolver::computeConcreteModel(LVRef v) {
    while (concrete_model.size() <= lva[v].ID())
        concrete_model.push(NULL);

    PTRef tr = lva[v].getPTRef();
    if (removed_by_GaussianElimination.has(tr)) {
        const ModelPoly &expr = removed_by_GaussianElimination[tr];
        Delta val;
        for (int i = 0; i < expr.size(); i++) {
            val += pta[expr[i]].coef * model.read(pta[expr[i]].var);
        }
        concrete_model[lva[v].ID()] = new opensmt::Real(val.R() + val.D() * delta);
    }
    else
        concrete_model[lva[v].ID()] = new opensmt::Real(model.read(v).R() + model.read(v).D() * delta);
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
    vec<PTRef> check_me;
    for (int i = 0; i < e.size(); i++) {
        check_me.push(e[i].sgn == l_False ? logic.mkNot(e[i].tr) : e[i].tr);
    }
//    printf("In PTRef this is %s\n", logic.pp(logic.mkAnd(check_me)));
    assert(logic.implies(logic.mkAnd(check_me), logic.getTerm_false()));
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

        Delta D;

        assert( !isModelOutOfBounds(v) );

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

//
// Add the variable x with the coefficient p_v to the polynomial represented by
// s
//
void LRASolver::addVarToRow( LVRef s, LVRef x, Real * p_v )
{
    assert(!lva[x].isBasic());
    assert(lva[s].isBasic());

    polyStore.add(lva[s].getPolyRef(), x, *p_v);
}

bool LRASolver::checkIntegersAndSplit( )
{
  assert(false);
/*

  assert( config.lra_integer_solver );
  assert( removed_by_GaussianElimination.empty( ) );

  VectorLAVar::const_iterator it = columns.begin( );
  LAVar * x;

  //  unsigned equality_counter=0;
  //  for( ; it != columns.end( ); ++it )
  //    if (( *it )->isEquality())
  //      equality_counter++;
  //
  //  cout << "Equalities in the complete integer check: " << equality_counter << " out of " << columns.size();

  it = columns.begin( );

  for( ; it != columns.end( ); ++it )
  {
    assert( !( *it )->skip );
    if( !( *it )->isModelInteger( ) )
    {
      x = *it;

      // Prepare the variable to store a splitting value
      Real * c = NULL;
      if( !numbers_pool.empty( ) )
      {
        c = numbers_pool.back( );
        numbers_pool.pop_back( );
      }
      else
      {
        c = new Real( 0 );
      }

      // Compute a splitting value
      if( x->M( ).R( ).get_den( ) != 1 )
      {
        if( x->M( ).R( ).get_num( ) < 0 )
          *c = x->M( ).R( ).get_num( ) / x->M( ).R( ).get_den( ) - 1;
        else
          *c = x->M( ).R( ).get_num( ) / x->M( ).R( ).get_den( );
      }
      else
      {
        if( x->M( ).D( ) < 0 )
          *c = x->M( ).R( ) - 1;
        else
          *c = x->M( ).R( );
      }

      // Check if integer splitting is possible for the current variable
      if( *c < x->L( ) && *c + 1 > x->U( ) )
      {
        vec<PTRef> tmp;
        getConflictingBounds( x, tmp);
        for (int i = 0; i < tmp.size; i++) {
            explanation.push(PtAsgn(tmp[i], getPolarity(tmp[i])));
        }
        for( unsigned i = 0; i < columns.size( ); ++i )
          if( !columns[i]->skip )
            columns[i]->restoreModel( );
        return setStatus( UNSAT );
      }

      vector<Enode *> splitting;

      // Prepare left branch
      Enode * or1 = egraph.mkLeq( egraph.cons( x->e, egraph.cons( egraph.mkNum( *c ) ) ) );
      LAExpression a( or1 );
      or1 = a.toEnode( egraph );
      egraph.inform( or1 );
      splitting.push_back( or1 );

      // Prepare right branch
      Enode * or2 = egraph.mkGeq( egraph.cons( x->e, egraph.cons( egraph.mkNum( *c + 1 ) ) ) );
      LAExpression b( or2 );
      or2 = b.toEnode( egraph );
      egraph.inform( or2 );
      splitting.push_back( or2 );

      //      cout << or1 <<endl;
      //      cout << or2 <<endl;
      // Push splitting clause
      egraph.splitOnDemand( splitting, id );

      // We don't need splitting value anymore
      numbers_pool.push_back( c );

      // We are lazy: save the model and return on the first splitting
      LAVar::saveModelGlobal( );
      checks_history.push_back( pushed_constraints.size( ) );
      return setStatus( SAT );
    }
  }
  // Cool! The model is already integer!
  LAVar::saveModelGlobal( );
  checks_history.push_back( pushed_constraints.size( ) );
  return setStatus( SAT );
*/
    return false;
}

// We may assume that the term is of the following forms
// (1) (* x c)
// (2) (* c x)
// (3) c
opensmt::Real LRASolver::evaluateTerm(PTRef tr)
{
    Pterm& t = logic.getPterm(tr);
    opensmt::Real val(0);
    // Case (3)
    if (logic.isRealConst(tr))
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
    if (!logic.hasSortReal(tr)) return ValPair_Undef;
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

//
// Destructor
//
LRASolver::~LRASolver( )
{
    tsolver_stats.printStatistics(cerr);
    // Remove numbers
    while( !numbers_pool.empty( ) )
    {
        assert( numbers_pool.back( ) );
        delete numbers_pool.back( );
        numbers_pool.pop_back( );
    }
}

bool LRASolver::valueConsistent(LVRef v)
{
    const Delta& value = model.read(v);
    Delta sum(0);
    PolyRef pr = lva[v].getPolyRef();
    for (int i = 0; i < polyStore.getSize(pr); i++) {
        const PolyTerm &t = pta[polyStore.readTerm(pr, i)];
        Pterm& smt_term = logic.getPterm(lva[t.var].getPTRef());


        sum += t.coef * model.read(t.var);
    }
    return value == sum;
}

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

