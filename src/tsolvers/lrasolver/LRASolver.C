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

LRASolver::LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d)
    : logic(l)
    , TSolver((SolverId)descr_lra_solver, (const char*)descr_lra_solver, c, d)
    , delta(Delta::ZERO)
    , bland_threshold(1000)
    , lavarStore(lva, numbers_pool)
{
    status = INIT;
    checks_history.push_back(0);
    first_update_after_backtrack = true;
}

void LRASolver::clearSolver()
{
    status = INIT;
    first_update_after_backtrack = true;
    delete lavarStore;
    pushed_constraints.clear();
    explanationCoefficients.clear();
    columns.clear();
    rows.clear();
    ptermToLVRef.clear();
    checks_history.clear();
    checks_history.push_back(0);
    touched_rows.clear();
    removed_by_GaussianElimination.clear();
    TSolver::clearSolver();

    lva.clear();
    pa.clear();
    ba.clear();

    lavarStore.clear();
}

const Delta& LRASolver::Ub(LVRef v) const
{
    LAVar& va = lva[v];
    LABoundList& bl = bla[va.getBL()];
    return ba[bl[va.ubound()]].getValue();
}

const Delta& LRASolver::Lb(LVRef v) const
{
    LAVar& va = lva[v];
    LABoundList& bl = bla[va.getBL()];
    return ba[bl[va.lbound()]].getValue();
}

//
// The model system
//
bool LRASolver::isModelOutOfBounds(LVRef v)
{
    return ( model[v] > Ub(v) || model[v] < Lb(v) );
}

bool LRASolver::isModelOutOfUpperBound(LVRef v)
{
    return ( model[v] > Ub(v) );
}

bool LRASolver::isModelOutOfLowerBound(LVRef v)
{
    return ( model[v] < Lb(v) );
}


const Delta LRASolver::overBound(LVRef v)
{
    assert( isModelOutOfBounds( ) );
    if (isModelOutOfUpperBound(v))
    {
        return ( Delta(model(v) - Ub(v)) );
    }
    else if ( isModelOutOfLowerBound(v) )
    {
        return ( Delta(Lb(v) - model(v)) );
    }
    assert (false);
}


bool LRASolver::isModelInteger(LVRef v) const
{
    return !( model[v].hasDelta() || !model[v].R().den_is_unit() );
}

bool LRASolver::isEquality(LVRef v) const
{
    return lva[v].lbound()+1 == lva[v].ubound() && !Lb(v).isInf() && !Ub(v).isInf() && Lb(v) == Ub(v);
}

bool LRASolver::isUnbounded(LVRef v) const
{
    return bla[lva[v].getBounds()].size() <= 2;
}

void LRASolver::unbindRow(LVRef v, int row)
{
    assert(lva[v].isBasic() || lva[v].getBoundedRowRef() != OccRef_Undef);
    boundedRowStore.remove(v, row);
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
    printf("Setting bound for %s\n", logic.printTerm(leq_tr));
    Pterm& leq = logic.getPterm(leq_tr);
    PTRef const_tr = leq[0];
    PTRef var_tr = leq[1];
    if (logic.isRealTimes(var_tr) || logic.isRealVar(var_tr)) {
        // The constraint is of the form
        // (1) cons <= var
        // (2) cons <= (-1)*var
        // parse the cons and (-1)*var or var
        BoundT bound_t; // Delta::LOWER in case (1), Delta::UPPER in case (2)

        if (logic.isRealVar(var_tr)) {
            bound_t = bound_l;
        }
        else {
            // This is an upper bound.  We need to revert the const_tr.
            bound_t = bound_u;

            // Make sure coef and var_tr are the correct way round.
            PTRef coef = logic.getPterm(var_tr)[0];
            var_tr = logic.getPterm(var_tr)[1];
            if (!logic.isConstant(coef)) {
                PTRef tmp = coef;
                coef = var_tr;
                var_tr = tmp;
            }
            assert(logic.mkRealNeg(logic.getTerm_RealOne()) == coef);

            const_tr = logic.mkRealNeg(const_tr);
        }

        assert(config.logic != QF_LRA || logic.isVar(var_tr));
        assert(config.logic != QF_LIA || logic.isVar(var_tr));
        assert(config.logic != QF_UFLRA || logic.isVar(var_tr) || logic.isUF(var_tr));

        // Get the lra var and set the mapping right.
        LVRef x = getLAVar(var_tr);
        Pterm& leq_t = logic.getPterm(leq_tr);
        if (leq_t.getId() >= (int)ptermToLVRef.size())
            ptermToLVRef.resize( leq_t.getId() + 1, NULL );
        ptermToLVRef[leq_t.getId()] = x;

        // Set the bound
        setBounds(x, leq_tr, logic.getRealConst(const_tr), bound_t);

    }
    else {
        // Cases (3) and (4)
        // The leq is of the form c <= (t1 + ... + tn).  Parse the sum term of the leq.
        // This needs a slack variable
        addSlackVar(leq_tr);

        Pterm& leq_t = logic.getPterm(leq_tr);

        PTRef const_tr = leq_t[0];
        PTRef sum_tr = leq_t[1];

        assert(logic.isRealConst(const_tr));
        assert(logic.isRealPlus(sum_tr));


    }
}

// Initialize columns and rows based on var s, and set the column id for
// s
void LRASolver::initSlackVar(LVRef s)
{
    lavarStore.notifyRow(s);

    // Update the rows
    if (lva[s].row_id() >= static_cast<int> (rows.size())) {
        rows.resize(lva[s].getRowId() + 1, NULL);
    }
    rows[lva[s].getRowId()] = s;
}


// I don't like this.  It probably leaks memory if numbers_pool is empty
void LRASolver::getReal(Real* r, PTRef cons)
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

// Get a possibly new non-basic LAVar for a PTRef.  Add the var
// immediately to a column.
LVRef LRASolver::getNBLAVar(PTRef var)
{
    LVRef x;
    // check if we need a new LAVar for a given var
    if (logic.getPterm(var).getId() >= (int)ptermToLVRef.size())
        ptermToLVRef.resize(logic.getPterm(var).getId() + 1, LVRef_Undef);

    if (ptermToLVRef[logic.getPterm(var).getId()] == LVRef_Undef) {
        x = lavarStore.getNewVar(var);
        if (lva[x].getColId() >= static_cast<int> ( columns.size() )) {
            columns.resize( lva[x].getColId() + 1, LVRef_Undef);
            tsolver_stats.num_vars = columns.size();
        }
        columns[lva[x].ColID()] = x;
        ptermToLVRef[logic.getPterm(var).getId()] = x;
    }
    else {
        x = ptermToLVRef[logic.getPterm(var).getId()];
    }
    return x;
}

// Return a slack var for the sum term tr_sum if it exists, otherwise create
// the slack var if it does not exist.  In case there exists a var s for
// the term tr_sum' = - tr_sum, return s and set reverse to true
LAVar* LRASolver::getSlackVar(PTRef tr_sum, bool &reverse)
{
    reverse = false;
    assert(logic.isRealPlus(tr_sum));

    int sum_id = logic.getPterm(tr_sum).getId();
    // First make sure the array contains an entry for the slack var
    if (sum_id >= (int)ptermToLVRef.size())
        ptermToLVRef.resize(sum_id + 1, NULL);

    // Then check if the var is non-null
    LVRef var = LVRef_Undef;
    if (ptermToLVRef[sum_id] != LVRef_Undef) {
        var = ptermToLavar[sum_id];
    }
    else {
        // There was no entry for the sum term
        PTRef tr_sump = logic.mkRealNeg(tr_sum);
        int tr_sump_id = logic.getPterm(tr_sump).getId();
        if (tr_sump_id < ptermToLVRef.size() && ptermToLVRef[tr_sump_id] != LVRef_Undef) {
            // Enable for the compact array
            var = ptermToLavar[tr_sump_id];
            reverse = true;
        }
    }
    return var;
}

void LRASolver::addSlackVar(PTRef leq_tr)
{
    // The leq is of the form c <= (t1 + ... + tn).  Parse the sum term of the leq.
    // This needs a slack variable

    BoundT bound_t;

    assert(logic.isRealLeq(leq_tr));
    Pterm& leq_t = logic.getPterm(leq_tr);

    PTRef const_tr = leq_t[0];
    PTRef sum_tr = leq_t[1];

    assert(logic.isRealConst(const_tr));
    assert(logic.isRealPlus(sum_tr));

    Pterm& t = logic.getPterm(sum_tr);
    int sum_id = t.getId();

    int leq_id = leq_t.getId();

    LVRef s;
    bool reverse;
    if ((s = getSlackVar(sum_tr, reverse)) == LVRef_Undef) {
        // The slack var for the sum did not exist previously.
        // Introduce the slack var with bounds.
        s = lavarStore.getNewVar(sum_tr);
        bound_t = bound_l;

        initSlackVar(s);
        assert( lva[s].getRowId() != -1 );

        if (sum_id >= (int)ptermToLavar.size())
            ptermToLVRef.resize(sum_id+1, NULL);
        ptermToLVRef[sum_id] = s;

        // Create the polynomial for the array
        makePolynomial(s, sum_tr);
    }
    else if (reverse) {
        // If reverse is true, the slack var negation exists.  We
        // need to add the mapping from the PTRef to the
        // corresponding slack var.
        const_tr = logic.mkRealNeg(const_tr);
        bound_t = bound_u;
    } else
        bound_t = bound_l;

    if (leq_id >= (int)ptermToLVRef.size())
        ptermToLVRef.resize(leq_id+1, NULL);
    ptermToLVRef[leq_id] = s;

    boundStore.addBound(s, leq_tr, logic.getRealConst(const_tr), bound_t);
    printf("  Added a slack var for %s: %d\n", logic.printTerm(sum_tr), LVA[s].ID());
}

// Create a polynomial to the slack var s from the polynomial pol
//
void LRASolver::makePolynomial(LVRef s, PTRef pol)
{
    // Create a polynomial for s
    Real * p_r;
    if (!numbers_pool.empty()) {
        p_r = numbers_pool.back();
        numbers_pool.pop_back();
        *p_r = Real(-1);
    }
    else {
        p_r = new Real(-1);
    }
    // Set -1*s to position 0 of the polynomial.  Why is that?
    lva[s].poly = polyStore.getPolynomial(s);

    Pterm& pol_t = logic.getPterm(pol);
    // reads the argument of +
    for (int i = 0; i < pol_t.size(); i++) {
        PTRef pr = pol_t[i];
        // Check the form of the term.  Can be either c * x or x for
        // Real constant c and real variable x.
        assert(logic.isRealTimes(pr) || logic.isRealVar(pr) || logic.isUF(pr));

        PTRef var;
        PTRef num;

        if (logic.isRealVar(pr) || logic.isUF(pr)) {
            // pr is of form x
            var = pr;
            num = logic.getTerm_RealOne();
        }
        else {
            // pr is of form c*x
            var = logic.getPterm(pr)[0];
            num = logic.getPterm(pr)[1];
            if (logic.isRealConst(var)) {
                PTRef tmp = num;
                num = var;
                var = tmp;
            }
        }
        assert(logic.isRealConst(num) && (logic.isRealVar(var) || logic.isUF(var)));

        // Get the coefficient
        if (!numbers_pool.empty()) {
            p_r = numbers_pool.back();
            numbers_pool.pop_back();
            *p_r = Real(logic.getRealConst(num));
        } else {
            p_r = new Real(logic.getRealConst(num));
        }

        // check if we need a new LAVar for a given var
        LVRef x = LVRef_Undef;

        int varId = logic.getPterm(var).getId();
        if (varId >= (int)ptermToLVRef.size())
            ptermToLVRef.resize(varId + 1, LVRef_Undef);

        if (ptermToLVRef[varId] != LVRef_Undef) {
            x = ptermToLavar[varId];
            addVarToRow(s, x, p_r);
        }
        else {
            x = lavarStore.getNewVar(var);
            ptermToLVRef[varId] = x;

            lva[x].setColId(columns.size());
            columns.push(x);
            tsolver_stats.num_vars = lva.getNumVars();

            int pos = pa[lva[s].poly].add(x, p_r);
            lva[x].binded_rows.add(x, pos);
        }

        assert(x != LVRef_Undef);
        assert(LVA[s].getRowIs() != -1);
    }
}

bool LRASolver::isValid(PTRef tr)
{
    return logic.isRealConst(tr) || logic.isRealPlus(tr) || logic.isRealMinus(tr) || logic.isRealNeg(tr) ||
           logic.isRealTimes(tr) || logic.isRealDiv(tr) || logic.isRealEq(tr) || logic.isRealLeq(tr) || logic.isRealLt(tr) ||
           logic.isRealGeq(tr) || logic.isRealGt(tr) || logic.isRealVar(tr);
}

//
// Reads the constraint into the solver
//
lbool LRASolver::declareTerm(PTRef leq_tr)
{
    if (informed(leq_tr)) return l_Undef;

    informed_PTRefs.insert(leq_tr, true);

    if (!logic.isRealLeq(leq_tr)) return l_Undef;
    printf("Declaring term %s\n", logic.printTerm(leq_tr));


    if (status != INIT)
    {
        // Treat the PTRef as it is pushed on-the-fly
        //    status = INCREMENT;
        assert( status == SAT );
    }
    assert(logic.isAtom(leq_tr));
    assert(logic.isRealLeq(leq_tr));
    Pterm& leq_t = logic.getPterm(leq_tr);

    // Terms are of form c <= t where
    //  - c is a constant and
    //  - t is either a term or a sum
    PTRef cons = leq_t[0];
    PTRef sum  = leq_t[1];
    Pterm& sum_t = logic.getPterm(sum);

    bool revert = false;

    assert(logic.isConstant(cons));
    assert(logic.isRealVar(sum) || logic.isRealTimes(sum) || logic.isRealPlus(sum));
    setBound(leq_tr);

    if (logic.hasSortBool(leq_tr)) {
        Pterm& t = logic.getPterm(leq_tr);
        while (known_preds.size() <= t.getId())
            known_preds.push(false);
        known_preds[t.getId()] = true;
    }
    else
        assert(false);

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

    (void)complete;
    // check if we stop reading constraints
    if (status == INIT)
        initSolver();

    LVRef x = NULL;

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
        VectorLAVar::const_iterator it = rows.begin();
        int max_var_id = lavarStore.numVars();
        int curr_var_id_x = max_var_id;
        for (int i = 0; i < rows.size(); i++) {
            LVRef it = rows[i];
            if (it == LVRef_Undef) continue; // There should not be nulls, since they result in quadratic slowdown?
            if (isModelOutOfBounds(it)) {
                if (bland_rule) {
                    bland_counter++;
                    tsolver_stats.num_bland_ops++;
                    // Select the var with the smallest id
                    x = lva[it].ID() < curr_var_id_x ? it : x;
                    curr_var_id_x = lva[it].ID() < curr_var_id_x ? lva[it]->ID() : curr_var_id_x;
                } else { // Use heuristics that prefer short polynomials
                    pivot_counter++;
                    tsolver_stats.num_pivot_ops++;
                    if (x == LVRef_Undef || (pa[lva[x].poly].size() > pa[lva[it].poly].size()))
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
            if (checks_history.back() < pushed_constraints.size())
                checks_history.push_back(pushed_constraints.size());
#ifdef GAUSSIAN_DEBUG
            computeModel();
#endif
//            cerr << "; USUAL SAT" << endl;
            setStatus(SAT);
            break;
//            return setStatus( SAT );
        }

        Real * a;
        LVRef y = LVRef_Undef;
        LVRef y_found = y;

        // Model doesn't fit the lower bound
        if (model[x] < Lb(x)) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the unbounding
            for (int i = 0; i < pa[lva[x].poly].size(); i++) {
                y = pa[lva[x].poly][i].var;
                assert( lva[y].isNonbasic() );
                a = pa[lva[x].poly][i].coef;
                if (x == y)
                    continue;

                assert(a != 0);
                const bool & a_is_pos = ( *a ) > 0;
                if ((a_is_pos && model[y] < Ub(y)) || (!a_is_pos && model[y] > Lb(y))) {
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
                    explanation.push(PtAsgn(tmp[i], getPolarity(tmp[i])));
                }
                setStatus(UNSAT);
                break;
//                return setStatus(UNSAT);
            }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
            else {
                if (bland_rule)
                    printf("pivoting on x-id %d and y-id %d\n", curr_var_id_x, curr_var_id_y);
                pivotAndUpdate(x, y_found, Lb(x));
            }
        } else if (model[x] > Ub(x) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the unbounding
            for (int i = 0; i < getPoly(x).size(); i++) {
                y = getPoly(x)[i].var
                if (x == y)
                    continue;
//                cerr << "; " << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                assert( lva[y].isNonbasic() );
                a = getPoly(x)[i].coef;
                assert(a != 0);
                const bool & a_is_pos = (*a) > 0;
                if ((!a_is_pos && model[y] < Ub(y)) || (a_is_pos && model[y] > Lb(y))) {
                    if (bland_rule) {
                        y_found = lva[y].ID() < curr_var_id_y ? y : y_found;
                        curr_var_id_y = lva[y].ID() < curr_var_id_y ? lva[y].ID() : curr_var_id_y;
                    } else {
                        if (y_found == NULL)
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
                for (int i = 0; i < tmp.size(); i++)
                    explanation.push(PtAsgn(tmp[i], getPolarity(tmp[i])));
                setStatus(UNSAT);
                break;
            }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
            else {
                if (bland_rule)
                    printf("pivoting on x-id %d and y-id %d\n", curr_var_id_x, curr_var_id_y);
                pivotAndUpdate(x, y_found, Ub(x));
            }
        } else {
            opensmt_error( "Error in bounds comparison" );
        }
    }
    getStatus() == true ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
    return getStatus();
}

//
// Push the constraint into the solver and increase the level
//
bool LRASolver::assertLit( PtAsgn pta, bool reason )
{
    ( void )reason;

    // Special cases of the "inequalitites"
    if (logic.isTrue(pta.tr) && pta.sgn == l_True) {
        tsolver_stats.sat_calls ++;
        return true;
    }
    if (logic.isFalse(pta.tr) && pta.sgn == l_False) {
        tsolver_stats.sat_calls ++;
        return true;
    }
    if (logic.isTrue(pta.tr) && pta.sgn == l_False) {
        tsolver_stats.unsat_calls ++;
        return false;
    }
    if (logic.isFalse(pta.tr) && pta.sgn == l_True) {
        tsolver_stats.unsat_calls ++;
        return false;
    }
    // check if we stop reading constraints
    if( status == INIT  )
        initSolver( );

    assert(pta.sgn != l_Undef);

//  cerr << "; Pushing (" << ( pta.sgn == l_False ? "not " : "") << logic.printTerm(pta.tr)
//       << " - " << ptermToLavar[logic.getPterm(pta.tr).getId()] << endl;

    bool is_reason = false;

    Pterm& t = logic.getPterm(pta.tr);

    // skip if it was deduced by the solver itself with the same polarity
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].polarity == pta.sgn && deduced[t.getVar()].deducedBy == id) {
        getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
        return getStatus( );
    }
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].deducedBy == id)
        is_reason = true; // This is a conflict!

    setPolarity(pta.tr, pta.sgn);

    LVRef it = ptermToLVRef[t.getId()];

    // Constraint to push was not found in local storage. Most likely it was not read properly before
    if ( it == NULL ) {
        std::cout << logic.printTerm(pta.tr) << "\n";
        throw "Unexpected push";
    }

    assert( !isUnbounded(it) );

    LABoundRefPair p = ptermToLABoundRefs[t.getId()];
    unsigned it_i = pta.sgn ? ba[p.neg].getIdx() : ba[p.pos].getIdx();
    // Assert only on the non-basic variables.  No check on the basic variables.
    if (assertBoundOnColumn( it, it_i ))
    {
        if (config.lra_theory_propagation == 1 && !is_reason)
            getSimpleDeductions(it, it_i);

        if (config.lra_check_on_assert != 0 && rand() % 100 < config.lra_check_on_assert)
        {
            // force solver to do check on assert with some probability
            return check( false );
        }
    }
    getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
    return getStatus( );
}

bool LRASolver::assertBoundOnColumn( LVRef it, unsigned it_i )
{
    assert( status == SAT );
    assert( it != LVRef_Undef );
    assert( isUnbounded(it) );
    const LAVarBound &itBound = getBound(it, it_i);

//  cerr << "; ASSERTING bound on " << *it << endl;

    // Check is simple SAT can be given
    if (((itBound.type() == bound_u) && it_i >= lva[it].ubound())
        || ((itBound.type() == bound_l) && it_i <= lva[it].lbound()))
    {
        if (checks_history.back() < pushed_constraints.size())
        {
            // cerr << "; PUSH CHECK " << checks_history.back( ) << " " << pushed_constraints.size( ) << endl;
            checks_history.push_back( pushed_constraints.size( ) );
        }
//    cerr << "; SIMPLE SAT" << endl;
        return getStatus();
    }
    // Check if simple UNSAT can be given
    if (((itBound.type() == bound_l) && ( it_i > lva[it].ubound() ))
     || ((itBound.bound_type == bound_u) && ( it_i < lva[it].lbound() )))
    {
        explanation.clear();
        explanationCoefficients.clear();

        if (itBound.type() == bound_u)
        {
            PTRef tr = ba[bla[lva[it].bounds()][lva[it].lbound()]].getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.push_back( Real( 1 ) );
        }
        else if (itBound.type() == bound_l)
        {
            PTRef tr = ba[bla[lva[it].bounds()][lva[it].ubound()]].getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.push_back( Real( 1 ) );
        }

        assert(itBound.getPTRef() != PTRef_Undef);
        explanation.push(PtAsgn(itBound.getPTRef(), getPolarity(itBound.getPTRef())));
        explanationCoefficients.push_back( Real( 1 ) );
        return setStatus( UNSAT );
    }

    // Update the Tableau data if needed
    if (lva[it].isNonbasic())
        update(it, itBound.getValue()));

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
    if (first_update_after_backtrack) {
        LATraceLim.push(LATrace.size());
//      cerr << "; re-apply " << pushed_constraints.size( ) << " - " << checks_history.back( ) << endl;
        for ( unsigned i = checks_history.back( ); i < pushed_constraints.size( ); i++ ) {
            LVRef v = pushed_constraints[i].v;
            if ( v != LVRef_Undef && LVA[v].isNonbasic() && isModelOutOfBounds(v) ) {
                if ( isModelOutOfUpperBound(v) )
                    update( v, LVA[v].U() );
                else
                    update( v, LVA[v].L() );
            }
        }
        first_update_after_backtrack = false;
    }

    // Update the generic deductions state
    TSolver::pushBacktrackPoint();
}

//
// Pop the solver one level up
//
void LRASolver::popBacktrackPoint( )
{
//  cerr << "; pop " << pushed_constraints.size( ) << endl;

    // Undo with history

    for (int i = LATrace[LATraceLim.last()]; i < LATrace.size(); i++) {
        LVRef var = LATrace[i];
        popModel(var);
    }
    LATrace.resize(LATraceLim.last());
    LATraceLim.pop();

    first_update_after_backtrack = true;

    pushed_constraints.pop_back( );

    setStatus(SAT);
    TSolver::popBacktrackPoint();
}

//
// Look for unbounded terms and applies Gaussian elimination to them.
// Delete the column if succeeded
//

void LRASolver::doGaussianElimination( )
{
    for (unsigned i = 0; i < columns.size( ); ++i) {
        assert(columns[i] != LVRef_Undef);
        LVRef x = columns[i];
        if (!lva[x].skip && !lva[x].isBasic() &&
            lva[x].isUnbounded() && bra[lva[x].getBindedRowsRef()].size() >= 2)
        {

            BindedRow& row = bra[lva[x].getBindedRowsRef()][0];
            LVRef basis = row.var;
            int pos = row.pos;
            int basisRow = lva[row.var].getRowId();

//            printf("; LAVar for column %d is %s and LAVar for the basis is %s\n", i, logic.printTerm(x->e), logic.printTerm(basis->e));
            Real a(pa[lva[basis].getPolyRef()][pos].coef);

//            printf("; Number of rows bound to %s is %d\n", logic.printTerm(basis->e), x->binded_rows.size());
            for (int j = 1; j < bra[lva[x].getBindedRowsRef()].size(); j++) {
                LVRef it_var = bra[lva[x].getBindedRowsRef()][j].var;
                int   it_pos = bra[lva[x].getBindedRowsRef()][j].pos;
                Real ratio(pa[lva[it_var].getPolyRef()][pos].coef / a);
                for (int k = 0; k < pa[lva[basis].getPolyRef()].size(); k++) {

                    LVRef poly_var = pa[lva[basis].getPolyRef()][k].var;
                    if (!pa[lva[it_var].getPolyRef()].has(poly_var)) {
                        // if poly_var is not in it_var's polynomial we
                        // multiply the coefficient of poly_var by it's coef/a
                        Real val(-ratio * (pa[lva[basis].getPolyRef()].find(poly_var).coef));
                        Real * c = NULL;
                        if (!numbers_pool.empty( )) {
                            c = numbers_pool.back( );
                            numbers_pool.pop_back( );
                            *c = val;
                        } else {
                            c = new Real(val);
                        }
                        int pos = pa[lva[it_var].getPolyRef()].add(poly_var, c);
                        bra[lva[poly_var].getBindedRowsRef()].add(it_var, pos)
                    } else {
                        // poly_var is in it_var's polynomial
                        PolyTerm& a_it = pa[lva[it_var].getPolyRef()].find(poly_var);
                        a_it.coef -= ( *( pa[lva[basis].getPolyRef()].find(poly_var).coef ) ) * ratio;
                        if (a_it.coef == 0) {
                            // Store removed Real in memory pool
                            numbers_pool.push_back( a_it.coef );
                            if (poly_var != x)
                                bra[lva[poly_var].getBindedRows()].remove(a_it.var);
                            pa[lva[it_var].getPolyRef()].remove(a_it.var);
                        }
                    }
                }
            }

            // Clear removed row
            for (int j = 0; j < pa[lva[basis].getPolyRef()].size(); j++) {
                PolyTerm &pt = pa[lva[basis].getPolyRef()][j];
                if (pt.var != basis)
                    bra[lva[pt.var].getBindedRowsRef()].remove(basis);
            }

            // Keep polynomial in x to compute a model later
            assert( lva[x].getPolyRef() == PRef_Undef );
            lva[x].setPolyRef(lva[basis].getPolyRef());
            lva[basis].getPolyRef() = PRef_undef;
            removed_by_GaussianElimination.push_back( x );
            bra[lva[x].getBindedRowsRef()].clear();
            lva[x].setSkip();

            // Replace basisRow slot with the last row in rows vector
            int m = rows.size() - 1;
            if (m > basisRow) {
                for (int j = 0; j < pa[lva[rows[m]].getPolyRef()].size(); j++) {
                    PolyTerm& pt = pa[lva[rows[m]].getPolyRef()][j];
                    if (pt.var != rows[m]) {
                        // We simply update the position here
                        bra[lva[pt.var].getBindedRowsRef()].remove(basis);
                        bra[lva[pt.var].getBindedRowsRef()].add(basis, pa[lva[rows[m]].getPolyRef()].getPos(pt.var));
                    }
                }
                assert(rows[m] != LVRef_Undef);
                rows[basisRow] = rows[m];
                lva[rows[m]].setBasic(basisRow);
            }
            lva[basis].setNonbasic();
            rows.pop_back( );
#ifdef GAUSSIAN_DEBUG
            printf("; Removed the row %s\n", logic.printTerm(LVA[basis].e));
            printf("; Removed column %s\n", logic.printTerm(LVA[x].e));
            printf("; rows: %d, columns: %d\n", rows.size(), nVars());
#endif
        }
    }
}

//
// updates the model values according to asserted bound
//
void LRASolver::update( LVRef x, const Delta & v )
{
    // update model value for all basic terms
    const Delta v_minusM = v - model[x];
    for (int i = 0; i < bra[lva[x].getBindedRowsRef()].size(); i++) {
        LVRef row = bra[lva[x].getBindedRowsRef()][i].var;
        int pos = bra[lva[x].getBindedRowsRef()][i].pos;
        model[row] += pa[lva[row].getPolyRef()][pos].coef * v_minusM;

        if ( static_cast<int> ( pa[lva[row].getPolyRef()].size( ) ) <= config.lra_poly_deduct_size )
              touched_rows.insert(row);

        //TODO: make a separate config value for suggestions
        //TODO: sort the order of suggestion requesting based on metric (Model increase, out-of-bound distance etc)
        //    if( config.lra_theory_propagation == 3 )
        //    {
        //      if( suggestions.empty( ) )
        //        rows[it->key]->getSuggestions( suggestions, id );
        //    }
    }
    model[x] = v;
//  cerr << "; UPDATED nonbasic " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;
}

//
// pivots x and y in solver and does all updates
//
void LRASolver::pivotAndUpdate( LVRef bv, LVRef nb, const Delta & v )
{
//  std::cerr << "; PIVOT AND UPDATE" << *bv << " - " << *nb << " - " << v << endl;
    assert( bv != nb );
    assert( lva[bv].isBasic() );
    assert( lva[nb].isNonbasic() );

    assert( lva[nb].getPolyRef() == PRef_Undef );
    assert( LVA[bv].binded_rows == RowRef_Undef );
    assert( pa[lva[bv].getPolyRef()].has(nb) );

    // get Theta (zero if Aij is zero)
    const Real & a = pa[lva[bv].getPolyRef()].find.(nb).coef;

    Delta theta(( v - model[bv] ) / a);

    // update models of nv and bv
    model[bv] = v;
    model[nb] += theta;

    int nb_pos = -1; // nb's position in bv's polynomial
    // update model of Basic variables
    for (int i = 0; i < bra[lva[nb].getBindedRowsRef()].size(); i++) {
        LVRef bv_other = bra[lva[nb].getBindedRowsRef()][i].var;
        int pos = LVA[nb].binded_rows[i].pos;
        if (bv_other != bv) {
            model[bv_other] *= pa[lva[bv_other].getPolyRef()][pos].coef * theta;
        }
        else {
            nb_pos = pos;
        }
    }
    assert(nb_pos != -1);

    // pivoting bv and nv

#if FAST_RATIONALS
    const Real inverse = -FastRational_inverse( a );
#else
    const Real inverse = -1 / a;
#endif

    // first change the attribute values for bv's polynomial
    for (int i = 0; i < pa[lva[bv].getPolyRef()].size(); i++)
        pa[lva[bv].getPolyRef()][i].coef *= inverse;

    // value of a_y should become -1
    assert( pa[lva[bv].getPolyRef()][nb_pos].coef == -1 );

    // now change the attribute values for all rows where nb was present
    for (int i = 0; i < bra[lva[nb].getBindedRowsRef()].size(); i++)
    {
        // Use LRASolver::addVarToRow?
        // check that the modified row is not x (it was changed already)
        if (bra[lva[nb].getBindedRowsRef()][i].var == x)
            continue;
        LVRef row = bra[lva[nb].getBindedRowsRef()][i].var;
        int   pos = bra[lva[nb].getBindedRowsRef()][i].pos;
        assert( pa[lva[row].getPolyRef()][pos].coef != 0 );

        // copy a to the new Real variable (use memory pool)
        //TODO: make a function for the code below
        Real * p_a = NULL;
        if (!numbers_pool.empty( ))
        {
            p_a = numbers_pool.back( );
            numbers_pool.pop_back( );
            *p_a = pa[lav[row]].getPolyRef()[pos].coef;
        }
        else
        {
            p_a = new Real( *( pa[lva[row].getPolyRef()][pos].coef ) );
        }

        const Real& a = *( p_a );

        // P_i = P_i + a_nv * P_bv (iterate over all elements of P_bv)
        for (int j = 0; pa[lva[bv].getPolyRef()].size(); j++) {
            LVRef col = pa[lva[bv].getPolyRef()][i].var;
            const Real &b = pa[lva[bv].getPolyRef()][i].coef;

            assert( b != 0 );

            // insert new element to P_i
            if (!pa[lva[row].getPolyRef()].has(col)) {
                // handle reals via memory pool
                Real * p_c = NULL;
                if (!numbers_pool.empty( )) {
                    p_c = numbers_pool.back( );
                    numbers_pool.pop_back( );
                    *p_c = a * b;
                }
                else {
                    p_c = new Real( a * b );
                }
                // Add the variable col with factor p_c to row's polynomial
                int poly_pos = pa[lva[row].getPolyRef()].add(col, p_c);
                // Update the list of appearances for col
                bra[lva[col].getBindedRowsRef()].add(row, poly_pos);
            }
            // or add to existing
            else {
                PolyTerm &polyt = pa[lva[row].getPolyRef()].find(col);
                polyt.coef += b * a;
                if ( polyt.coef == 0 ) {
                    // delete element from P_i if it became 0
                    // Save Real in pool
                    numbers_pool.push_back( polyt.coef );

                    // Mark out the value from column and row
                    if (col != nb)
                        bra[lva[col].getBindedRowsRef()].remove(row);
                    pa[lva[row].getPolyRef()].remove(col);
                }
            }
        }
        numbers_pool.push_back( p_a );
        assert( !pa[lva[row].getPolyRef()].has(bv) );
    }

    // swap x and y (basicID, polynomial, bindings)
    lva[nv].setPolyRef(lva[bv].getPolyRef());
    lva[bv].setPolyRef(PolyRef_Undef);
    LVA[bv].setNonbasic();
    lva[nv].setRowId(lva[bv].getRowRef());

    rows[lva[nv].getRowId()] = nv;

    assert( !pa[lva[nb].getPolyRef()].has(bv) );
    assert( pa[lva[nb].getPolyRef()].find(bv).pos >= 0 );
    assert( pa[lva[nb].getPolyRef()].has(bv) );
    PolyTerm &pt = pa[lva[nb].getPolyRef()].find(bv);
    pt.pos = bra[lva[bv].getBindedRowsRef()].size();
    bra[lva[bv].getBindedRowsRef()].add(nv, pa[lva[nv].getPolyRef()].getPos(bv))
    bra[lva[nv].getBindedRowsRef()].clear();

    assert( pa[lva[bv].getPolyRef()].size() == 0 );
    assert( pa[lva[nb].getPolyRef()].size() > 0 );
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
        // Gaussian Elimination should not be performed in the Incremental mode!
        if (config.lra_gaussian_elim == 1 && config.do_substitutions())
            doGaussianElimination();

        boundStore.buildBounds(ptermToLABoundRefs);

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
    LVRef y;
    if (model[x] < Lb(x)) {
        // add all bounds for polynomial elements, which limit lower bound
        for (int i = 0; i < pa[lva[x].getPolyRef()].size(); i++) {
            PolyTerm &pt = pa[lva[x].getPolyRef()];
            const Real &a = *(pt.coef);
            assert( a != 0 );
            y = columns[pt.var];
            if (x == y) {
                PTRef my_bound = ba[bla[lva[y].getBounds()][lba[y].lbound()]].getPTRef();
                assert(my_bound != PTRef_Undef);

                dst.push(my_bound);
                explanationCoefficients.push_back( Real( 1 ) );
            }
            else if (a < 0) {
                LABoundRef l_bound = bla[lva[y].getBounds()][lba[y].lbound()];
                assert(l_bound != LABoundRef_Infty);
                assert(ba[l_bound].getPTRef() != PTRef_Undef);

                dst.push(ba[l_bound].getPTRef());
                explanationCoefficients.push_back( -a );
            }
            else {
                LABoundRef u_bound = bla[lva[y].getBounds()][lba[y].ubound()];
                assert( u_bound != LABoundRef_Infty );
                assert( ba[u_bound].getPTRef() != PTRef_Undef );

                dst.push(ba[u_bound].getPTRef());
                explanationCoefficients.push_back(a);
            }
        }
    }
    if (model[x] > Ub(x)) {
        // add all bounds for polynomial elements, which limit upper bound
        for (int i = 0; i < pa[lva[x].getPolyRef()].size(); i++) {
            PolyTerm &pt = pa[lva[x].getPolyRef()];
            const Real &a = *(pt.coef);
            assert( a != 0 );
            y = columns[pt.var];
            if (x == y) {
                PTRef my_bound = ba[bla[lva[y].getBounds()][lba[y].ubound()]].getPTRef();
                assert(my_bound != PTRef_Undef);

                dst.push(my_bound);
                explanationCoefficients.push_back( Real( 1 ) );
            }
            else if (a > 0) {
                LABoundRef l_bound = bla[lva[y].getBounds()][lba[y].lbound()];
                assert(l_bound != LABoundRef_Infty);
                assert( ba[l_bound()].getPTRef() != PTRef_Undef );

                dst.push( ba[l_bound].getPTRef() );
                explanationCoefficients.push_back( a );
            }
            else {
                LABoundRef u_bound = bla[lva[y].getBounds()][lba[y].ubound()];
                assert( u_bound != LABoundRef_Infty );
                assert( ba[u_bound].getPTRef() != PTRef_Undef );

                dst.push(ba[u_bound].getPTRef());
                explanationCoefficients.push_back(-a);
            }
        }
    }

    assert( dst.size() == pa[lva[x].getPolyRef()].size() );

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

void LRASolver::getSimpleDeductions(LVRef v, int bound_idx)
{
    LABoundList& bound_list = bla[lva[v].getBounds()];
    LABoundRef br = bound_list[bound_idx];
    if (br == LABoundRef_Infty) return;
    LABound& bound = ba[br];
    if (bound.getType() == bound_l) {
        assert(lva[v].lbound() > 0);
        for (int it = lva[v].lbound() - 1; it > 0; it--) {
            LABound& bound_prop = ba[bound_list[it]];
            if ((bound_prop.getType() == bound_l) &&
                !hasPolarity(bound_prop.getPTRef()) &&
                deduced[logic.getPterm(bound_prop).getVar()] == l_Undef)
            {
                lbool pol = bound_prop.getSign() ? l_False : l_True;
                deduced[logic.getPterm(bound_prop).getVar()] = DedElem(solver_id, pol);
                th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
            }
        }
    }
    else if (bound.getType() == bound_u) {
        for (int it = lva[v].ubound() + 1; it < bound_list.size() - 1; i++) {
            LABound& bound_prop = ba[bound_list[it]];
            if ((bound_prop.getType == bound_u) &&
                !hasPolarity(bound_prop.getPTRef()) &&
                (deduced[logic.getPterm(bound_prop).getVar()]== l_Undef))
            {
                lbool pol = bound_prop.getSign() ? l_False : l_True;
                deduced[logic.getPterm(bound_prop).getVar()] = DedElem(solver_id, pol);
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
    out << "Bounds:" << endl;

    // print bounds array size
    for (unsigned i = 0; i < columns.size(); i++)
        out << bla[columns[i].getBounds()].size() << "\t";
    out << endl;

    // print the upper bounds
    for ( unsigned i = 0; i < columns.size(); i++)
        ba.printBound(bla[lva[columns[i]].getBounds()][lva[columns[i]].ubound()]);
    out << endl;

    // print the lower bounds
    for ( unsigned i = 0; i < columns.size(); i++ )
        ba.printBound(bla[lva[columns[i]].getBounds()][lva[columns[i]].lbound()]);
        out << ba[bla[lva[columns[i]].getBounds()][lva[columns[i]].lbound()]] << "\t";
    out << endl;

    // print current non-basic variables
    out << "Var:" << endl;
    for ( unsigned i = 0; i < columns.size(); i++ )
        out << logic.printTerm(lva[columns[i]].e) << "\t";
    out << endl;

    // print current model values
    out << "Model:" << endl;
    for ( unsigned i = 0; i < columns.size(); i++)
        out << model[columns[i]] << "\t";
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
            if ( pa[lva[rows[i]].getPolyRef()].has(columns[j]) )
                out << pa[lva[rows[i]].getPolyRef()].find(columns[j]).coef;
            out << "\t";
        }
        out << endl;
    }
}

//
// Detect the appropriate value for symbolic delta and stores the model
//
void LRASolver::computeModel( )
{
    assert( status == SAT );

    Real minDelta( 0 );
    Real maxDelta( 0 );
    Real curDelta( 0 );
    Delta curBound( Delta::ZERO );
    LVRef col;

    //
    // For all columns check the min/max value for delta
    // Note, it should be always that min > 0 and max < 0
    //
    for (unsigned i = 0; i < columns.size( ); ++i)
    {
        if (lva[columns[i]].skip())
            continue;
#ifdef GAUSSIAN_DEBUG
        printf("computing model for %s (%d)\n", logic.printTerm(lva[columns[i]].e), lva[columns[i]].e.x);
        cerr << "Its M is " << model[columns[i]] << '\n';
        cerr << "Its bounds are [" << ba.printBound(bla[lva[columns[i]].getBounds()][lva[columns[i]].lbound()]) << ", " << ba.printBound(bla[lva[columns[i]].getBounds()][lva[columns[i]].ubound()]) << "]" << '\n';
#endif
        col = columns[i];
        assert( !isModelOutOfBounds(col) );

        curDelta = 0;
        curBound = Delta( Delta::ZERO );

        // Check if the lower bound can be used and at least one of delta and real parts are not 0
        if ( boundStore.getLowerBound(col) != LABoundRef_Infty
            && ( ba[boundStore.getLowerBound(col)].getValue().D() != 0 || model[col].D() != 0 )
            && ( ba[boundStore.getLowerBound(col)].getValue().R() != 0 || model[col].R() != 0 ) )
        {
            curBound = ba[boundStore.getLowerBound(col)].getValue() - model[col];

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
        // Check if the upper bound can be used and at least one of delta and real parts are not 0
        if ( boundStore.getUpperBound(col) != LABoundRef_Infty
            && ( ba[boundStore.getUpperBound(col)].getValue().D() != 0 || model[col].D() != 0 )
            && ( ba[boundStore.getUpperBound(col)].getValue().R() != 0 || model[col].R() != 0 ) )
        {
            curBound = model[col] - ba[boundStore.getUpperBound(col)].getValue();

            // if delta is > 0 then use delta for min
            if ( curBound.D() > 0 )
            {
                curDelta = -(curBound.R() / curBound.D() );
                if ( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
                    minDelta = curDelta;
            }
            // if denominator is < 0 than use delta for max
            else if ( curBound.D() < 0 )
            {
                curDelta = -(curBound.R() / curBound.D());
                if ( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
                    maxDelta = curDelta;
            }
        }
    }

    // TODO: check if it is it really true :)
    assert( minDelta >= 0 );
    assert( maxDelta <= 0 );
    delta = ( minDelta ) / 2;

#ifdef GAUSSIAN_DEBUG
    cerr << "; delta: " << curDelta << '\n';
#endif

    // Compute the value for each variable. Delta is taken into account
    for ( unsigned i = 0; i < columns.size( ); ++i )
        computeConcreteModel(columns[i], curDelta);

    // Compute the value for each variable deleted by Gaussian elimination
    while ( !removed_by_GaussianElimination.empty( ) )
    {
        LVRef x = removed_by_GaussianElimination.back( );
        Real div = 0;
        Delta v_delta(0);

        for (int i = 0; i < pa[lva[x].getPolyRef()].size(); i++)
        {
            PolyTerm &pt = pa[lva[x].getPolyRef()][i];

            col = columns[pt.var];
            if ( col != x ) {
                v_delta += *(pt.coef) * model[col];
            }
            else {
                div -= *( pt.coef );
            }
        }
        assert( div != 0 );
        model[x] = v_delta/div;
//        cout << "value of " << logic.printTerm(x->e) << " is " << x->M() << endl;

        removed_by_GaussianElimination.pop_back( );
    }
}

// Fill the vector with the vars removed due to not having bounds
const void LRASolver::getRemoved(vec<PTRef>& removed) const
{
    for (int i = 0; i < removed_by_GaussianElimination.size(); i++)
        removed.push(lva[removed_by_GaussianElimination[i]].e);
}

//
// Add the variable x with the coefficient p_v to the row represented by
// s
//
void LRASolver::addVarToRow( LVRef s, LVRef x, Real * p_v )
{
    assert(!lva[x].isBasic());
    assert(lva[s].isBasic());

    if (pa[lva[s].getPolyRef()].has(x)) {
        PolyTerm &pt = pa[lva[s].getPolyRef()].find(x);
        pt.coef += *p_v;
        if (pt.coef == 0) {
            numbers_pool.push_back(pt.coef);
            bra[lva[x].getBindedRowsRef()].remove(s);
            pa[lva[s].getPolyRef()].remove(x);
        }
    }
    else {
        int pos = pa[lva[s].getPolyRef()].add(x, p_v);
        bra[lva[x].getBindedRowsRef()]..add(s, pos);
    }
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

ValPair LRASolver::getValue(PTRef tr)
{
    if (!logic.hasSortReal(tr)) return ValPair_Undef;
    int id = logic.getPterm(tr).getId();
    if (id < ptermToLavar.size() && ptermToLavar[id] != NULL) {
        const Delta &v = model[ptermToLavar[id]];
        for (int i = 0; i < removed_by_GaussianElimination.size(); i++) {
            if (tr == lva[removed_by_GaussianElimination[i]].e)
                printf("Var %s removed by Gaussian elimination\n", logic.printTerm(tr));
        }
        opensmt::Real val(v.R() + v.D() * delta);
        return ValPair(tr, val.get_str().c_str());
    }
    return ValPair_Undef;
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
            // In this one I have no idea why LAExpression swaps the
            // sign.  But we want it unswapped again, so we negate.
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
            // In this one I have no idea why LAExpression swaps the
            // sign.  But we want it unswapped again, so we negate.
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

