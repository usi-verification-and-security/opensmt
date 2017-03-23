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
{
    lavarStore = new LAVarStore(*this, deduced, numbers_pool);
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
    ptermToLavar.clear();
    checks_history.clear();
    checks_history.push_back(0);
    touched_rows.clear();
    removed_by_GaussianElimination.clear();
    TSolver::clearSolver();


    lavarStore = new LAVarStore(*this, deduced, numbers_pool);
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
    Pterm& leq = logic.getPterm(leq_tr);
    PTRef const_tr = leq[0];
    PTRef var_tr = leq[1];
    if (logic.isRealTimes(var_tr) || logic.isRealVar(var_tr)) {
        // The constraint is of the form
        // (1) cons <= var
        // (2) cons <= (-1)*var or
        // parse the cons and (-1)*var or var
        Delta::deltaType bound_t; // Delta::LOWER in case (1), Delta::UPPER in case (2)

        if (logic.isRealVar(var_tr)) {
            bound_t = Delta::LOWER;
        }
        else {
            // This is an upper bound.  We need to revert the const_tr.
            bound_t = Delta::UPPER;

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
        LAVar * x = getLAVar(var_tr);
        Pterm& leq_t = logic.getPterm(leq_tr);
        if (leq_t.getId() >= (int)ptermToLavar.size())
            ptermToLavar.resize( leq_t.getId() + 1, NULL );
        ptermToLavar[leq_t.getId()] = x;

        // Set the bound
        x->setBounds(leq_tr, logic.getRealConst(const_tr), bound_t);

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
void LRASolver::initSlackVar(LAVar* s)
{
    lavarStore->notifyRow(s);

    // Update the columns
    if (s->ID() >= static_cast<int>(columns.size())) {
        columns.resize(s->ID() + 1, NULL);
        tsolver_stats.num_vars = columns.size();
    }
    columns[s->ID()] = s;

    // Update the rows
    if (s->basicID() >= static_cast<int> (rows.size())) {
        rows.resize(s->basicID() + 1, NULL);
    }
    rows[s->basicID()] = s;
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

// Get a possibly new LAVar for a PTRef
LAVar* LRASolver::getLAVar(PTRef var)
{
    LAVar* x;
    // check if we need a new LAVar for a given var
    if (logic.getPterm(var).getId() >= (int)ptermToLavar.size())
        ptermToLavar.resize(logic.getPterm(var).getId() + 1, NULL);

    if (ptermToLavar[logic.getPterm(var).getId()] == NULL) {
//        assert( status == INIT );

        //x = lavarStore->getNewVar(leq_tr, var, *p_v, revert);
        x = lavarStore->getNewVar(var);
        if (x->ID() >= static_cast<int> ( columns.size() )) {
            columns.resize( x->ID( ) + 1, NULL );
            tsolver_stats.num_vars = columns.size();
        }
        columns[x->ID( )] = x;
        ptermToLavar[logic.getPterm(var).getId()] = x;
    }
    else {
        x = ptermToLavar[logic.getPterm(var).getId()];
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
    if (sum_id >= (int)ptermToLavar.size())
        ptermToLavar.resize(sum_id + 1, NULL);

    // Then check if the var is non-null
    LAVar* var = NULL;
    if (ptermToLavar[sum_id] != NULL) {
        var = ptermToLavar[sum_id];
    }
    else {
        // There was no entry for the sum term
        PTRef tr_sump = logic.mkRealNeg(tr_sum);
        int tr_sump_id = logic.getPterm(tr_sump).getId();
        if (tr_sump_id < ptermToLavar.size() && ptermToLavar[tr_sump_id] != NULL) {
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

    Delta::deltaType bound_t;

    assert(logic.isRealLeq(leq_tr));
    Pterm& leq_t = logic.getPterm(leq_tr);

    PTRef const_tr = leq_t[0];
    PTRef sum_tr = leq_t[1];

    assert(logic.isRealConst(const_tr));
    assert(logic.isRealPlus(sum_tr));

    Pterm& t = logic.getPterm(sum_tr);
    int sum_id = t.getId();

    int leq_id = leq_t.getId();

    LAVar * s;
    bool reverse;
    if ((s = getSlackVar(sum_tr, reverse)) == NULL) {
        // The slack var for the sum did not exist previously.
        // Introduce the slack var with bounds.
        s = lavarStore->getNewVar(sum_tr);
        bound_t = Delta::LOWER;

        initSlackVar(s);
        assert( s->basicID() != -1 );


        if (sum_id >= (int)ptermToLavar.size())
            ptermToLavar.resize(sum_id+1, NULL);
        ptermToLavar[sum_id] = s;

        // Create the polynomial for the array
        makePolynomial(s, sum_tr);
    }
    else if (reverse) {
        // If reverse is true, the slack var negation exists.  We
        // need to add the mapping from the PTRef to the
        // corresponding slack var.
        const_tr = logic.mkRealNeg(const_tr);
        bound_t = Delta::UPPER;
    } else
        bound_t = Delta::LOWER;

    if (leq_id >= (int)ptermToLavar.size())
        ptermToLavar.resize(leq_id+1, NULL);
    ptermToLavar[leq_id] = s;

    s->setBounds(leq_tr, logic.getRealConst(const_tr), bound_t);
}

// Create a polynomial to the slack var s from the polynomial pol
//
void LRASolver::makePolynomial(LAVar* s, PTRef pol)
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
    // Set -1 to position 0 of the polynomial.  Why is that?
    s->polynomial.add(s->ID(), 0, p_r);

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
        LAVar * x = NULL;

        int varId = logic.getPterm(var).getId();
        if (varId >= (int)ptermToLavar.size())
            ptermToLavar.resize(varId + 1, NULL);

        if (ptermToLavar[varId] != NULL) {
            x = ptermToLavar[varId];
            addVarToRow(s, x, p_r);
        }
        else {
            x = lavarStore->getNewVar(var);
            ptermToLavar[varId] = x;

            if (x->ID() >= static_cast<int> (columns.size())) {
                columns.resize(x->ID() + 1, NULL);
                tsolver_stats.num_vars = columns.size();
            }
            columns[x->ID()] = x;

            x->binded_rows.add(s->basicID(), s->polynomial.add(x->ID(), x->binded_rows.free_pos(), p_r));
        }

        assert(x);
        assert(s->basicID() != -1);
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

    if (logic.isRealTimes(sum) || logic.isRealVar(sum)) {
        setBound(leq_tr);
    }
    // parse the Plus term of the contraint
    else if (logic.isRealPlus(sum)) {
        // The leq is of the form c <= (t1 + ... + tn).  Parse the sum term of the leq.
        // This needs a slack variable
        setBound(leq_tr);
    }
    else {
        assert(false);
    }

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
//    opensmt::StopWatch check_timer(tsolver_stats.simplex_timer);

    (void)complete;
    // check if we stop reading constraints
    if (status == INIT)
        initSolver();

    LAVar * x = NULL;

    VectorLAVar hist_x;
    VectorLAVar hist_y;
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

        x = NULL;

        if (!bland_rule && (repeats > columns.size()))
            bland_rule = true;

        // look for the basic x with the smallest index which doesn't fit the bounds
        // XXX Keep these in a heap, so that there's no need to go over all
        // of them every time!
        VectorLAVar::const_iterator it = rows.begin();
        int max_var_id = lavarStore->numVars();
        int curr_var_id_x = max_var_id;
        for (; it != rows.end(); ++it) {
            if ((*it) == NULL) continue; // There should not be nulls, since they result in quadratic slowdown?
            if ((*it)->isModelOutOfBounds()) {
                if (bland_rule) {
                    bland_counter++;
                    tsolver_stats.num_bland_ops++;
                    // Select the var with the smallest id
                    x = (*it)->ID() < curr_var_id_x ? *it : x;
                    curr_var_id_x = (*it)->ID() < curr_var_id_x ? (*it)->ID() : curr_var_id_x;
                } else { // Use heuristics that prefer short polynomials
                    pivot_counter++;
                    tsolver_stats.num_pivot_ops++;
                    if (x == NULL)
                        x = *it;
                    else if (x->polynomial.size() > (*it)->polynomial.size())
                        x = *it;
                }
            }
        }

        if (x == NULL) {
            // If not found, check if problem refinement for integers is required
            if (config.lra_integer_solver && complete)
                return checkIntegersAndSplit( );

            // Otherwise - SAT
            refineBounds( );
            LAVar::saveModelGlobal( );
            if (checks_history.back() < pushed_constraints.size())
                checks_history.push_back(pushed_constraints.size());
//            cerr << "; USUAL SAT" << endl;
            setStatus(SAT);
            break;
//            return setStatus( SAT );
        }

        Real * a;
        LAVar * y = NULL;
        LAVar * y_found = NULL;

        // Model doesn't fit the lower bound
        if (x->M() < x->L() ) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the unbounding
            LARow::iterator it = x->polynomial.begin();
            for (; it != x->polynomial.end(); x->polynomial.getNext(it)) {
                y = columns[it->key];
                if (x == y)
                    continue;
//                cerr << "; " << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                assert( y->isNonbasic( ) );
                a = it->coef;
                assert(a != 0);
                const bool & a_is_pos = ( *a ) > 0;
                if ((a_is_pos && y->M() < y->U()) || (!a_is_pos && y->M() > y->L())) {
                    if (bland_rule) {
                        // Choose the leftmost nonbasic variable with a negative (reduced) cost
                        y_found = y->ID() < curr_var_id_y ? y : y_found;
                        curr_var_id_y = y->ID() < curr_var_id_y ? y->ID() : curr_var_id_y;
                    } else {
                        if (y_found == NULL)
                            y_found = y;
                        else if (y_found->binded_rows.size() > y->binded_rows.size()) // heuristic favoring more independent vars
                            y_found = y;
                    }
                }
            }

            // if it was not found - UNSAT
            if (y_found == NULL) {
//                cerr << "; NO ways to SAT" << endl;
                vec<PTRef> tmp;
                getConflictingBounds(x, tmp);
                for (int i = 0; i < tmp.size(); i++) {
                    explanation.push(PtAsgn(tmp[i], getPolarity(tmp[i])));
                }
                // TODO: Keep the track of updated models and restore only them
                for (unsigned i = 0; i < columns.size(); ++i)
                    if (!columns[i]->skip)
                        columns[i]->restoreModel();
                setStatus(UNSAT);
                break;
//                return setStatus(UNSAT);
            }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
            else {
                if (bland_rule)
                    printf("pivoting on x-id %d and y-id %d\n", curr_var_id_x, curr_var_id_y);
                pivotAndUpdate(x, y_found, x->L());
            }
        } else if (x->M() > x->U()) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the unbounding
            LARow::iterator it = x->polynomial.begin( );
            for (; it != x->polynomial.end(); x->polynomial.getNext(it)) {
                y = columns[it->key];
                if (x == y)
                    continue;
//                cerr << "; " << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                assert( y->isNonbasic( ) );
                a = it->coef;
                assert(a != 0);
                const bool & a_is_pos = (*a) > 0;
                if ((!a_is_pos && y->M() < y->U()) || (a_is_pos && y->M() > y->L())) {
                    if (bland_rule) {
                        y_found = y->ID() < curr_var_id_y ? y : y_found;
                        curr_var_id_y = y->ID() < curr_var_id_y ? y->ID() : curr_var_id_y;
                    } else {
                        if (y_found == NULL)
                            y_found = y;
                        else if (y_found->binded_rows.size() > y->binded_rows.size())
                            y_found = y;
                    }
                }
            }

            // if it was not found - UNSAT
            if (y_found == NULL) {
//              cerr << "; NO ways to SAT 2" << endl;
                // add the x to explanations
                vec<PTRef> tmp;
                getConflictingBounds(x, tmp);
                for (int i = 0; i < tmp.size(); i++)
                    explanation.push(PtAsgn(tmp[i], getPolarity(tmp[i])));
                for (unsigned i = 0; i < columns.size(); ++i)
                    if (!columns[i]->skip)
                        columns[i]->restoreModel();
                setStatus(UNSAT);
                break;
//                return setStatus(UNSAT);
            }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
            else {
                if (bland_rule)
                    printf("pivoting on x-id %d and y-id %d\n", curr_var_id_x, curr_var_id_y);
                pivotAndUpdate(x, y_found, x->U());
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
  if ( deduced[t.getVar()] != l_Undef && deduced[t.getVar()].deducedBy == id)
    is_reason = true; // This is a conflict!

  setPolarity(pta.tr, pta.sgn);

  LAVar* it = ptermToLavar[t.getId()];

  // Constraint to push was not found in local storage. Most likely it was not read properly before
  if ( it == NULL ) {
      std::cout << logic.printTerm(pta.tr) << "\n";
      throw "Unexpected push";
  }

  assert( !it->isUnbounded( ) );
  unsigned it_i = it->getIteratorByPTRef( pta.tr, pta.sgn == l_False );

  if( assertBoundOnColumn( it, it_i ) )
  {
    if( config.lra_theory_propagation == 1 && !is_reason )
    {
      it->getSimpleDeductions(th_deductions, it->all_bounds[it_i].bound_type, id);
    }
    if( config.lra_check_on_assert != 0 && rand( ) % 100 < config.lra_check_on_assert )
    {
      // force solver to do check on assert with some probability
      return check( false );
    }
  }
  getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
  return getStatus( );
}

////
//// Push the constraint into the solver and increase the level
////
//bool LRASolver::assertLitPolarity( Enode * e, bool polarity, bool is_reason )
//{
//
//  ( void )is_reason;
//  // check if we stop reading constraints
//  if( status == INIT )
//    initSolver( );
//
//  //  assert( e->hasPolarity( ) );
//
//  cerr << "Pushing (" << ( e->getPolarity( ) == l_True ) << ") (" << ( e->getDeduced( ) == l_True ) << ")  [" << e->getDedIndex( ) << "/" << id << "] " << e
//      << " - " << PTermToLavar[e->getId( )] << endl;
//
//  //  bool is_reason = false;
//  //
//  //  // skip if it was deduced by the solver itself with the same polarity
//  //  if( e->isDeduced( ) && e->getDeduced( ) == e->getPolarity( ) && e->getDedIndex( ) == id )
//  //    return getStatus( );
//  //  else if( e->isDeduced( ) && e->getDedIndex( ) == id )
//  //    is_reason = true;
//
//  assert( status != UNSAT );
//
//  // Look for the constraint to push
//  LAVar* it = ptermToLavar[e->getId( )];
//
//  if( it != NULL )
//  {
//    assert( !it->isUnbounded( ) );
//    unsigned it_i = it->getIteratorByEnode( e, !polarity );
//
//    if( !assertBoundOnColumn( it, it_i ) )
//    {
//      if( config.lra_theory_propagation == 1 && !is_reason )
//      {
//        it->getSimpleDeductions( th_deductions, id, itBound.bound_type );
//      }
//    }
//    return getStatus( );
//
////    if( config.lra_check_on_assert != 0 && rand( ) % 100 < config.lra_check_on_assert )
////    {
////      // force solver to do check on assert with some probability
////      return check( false );
////    }
////    else
//
//  }
//  // Constraint to push was not find in local storage. Most likely it was not read properly before
//  else
//  {
//    error( "Unexpected push! ", "" );
//    return setStatus( ERROR );
//  }
//}

bool LRASolver::assertBoundOnColumn( LAVar * it, unsigned it_i )
{
  assert( status == SAT );
  assert( it != NULL );
  assert( !it->isUnbounded( ) );
  LAVar::LAVarBound &itBound = it->all_bounds[it_i];

//  cerr << "; ASSERTING bound on " << *it << endl;

  // Check is simple SAT can be given
  if( ( (itBound.bound_type == bound_u) && it_i >= it->u_bound ) || ( (itBound.bound_type == bound_l) && it_i <= it->l_bound ) )
  {
    if( checks_history.back( ) < pushed_constraints.size( ) )
    {
//      cerr << "; PUSH CHECK " << checks_history.back( ) << " " << pushed_constraints.size( ) << endl;
      checks_history.push_back( pushed_constraints.size( ) );
    }
//    cerr << "; SIMPLE SAT" << endl;
    return getStatus( );
  }
  // Check if simple UNSAT can be given
  if( ( (itBound.bound_type == bound_l) && ( it_i > it->u_bound ) ) || ( (itBound.bound_type == bound_u) && ( it_i < it->l_bound ) ) )
  {
    explanation.clear( );
    explanationCoefficients.clear( );

    if( (itBound.bound_type == bound_u) && it->all_bounds[it->l_bound].e != PTRef_Undef )
    {
//      explanation.push(PtAsgn(it->all_bounds[it->l_bound].e, l_True));
      PTRef tr = it->all_bounds[it->l_bound].e;
      explanation.push(PtAsgn(tr, getPolarity(tr)));
      explanationCoefficients.push_back( Real( 1 ) );
    }
    else if( (itBound.bound_type == bound_l) && it->all_bounds[it->u_bound].e != PTRef_Undef )
    {
//      explanation.push(PtAsgn(it->all_bounds[it->u_bound].e, l_True));
      PTRef tr = it->all_bounds[it->u_bound].e;
      explanation.push(PtAsgn(tr, getPolarity(tr)));
      explanationCoefficients.push_back( Real( 1 ) );
    }

    if( itBound.e != PTRef_Undef )
    {
//      explanation.push(PtAsgn(itBound.e, l_True));
      explanation.push(PtAsgn(itBound.e, getPolarity(itBound.e)));
      explanationCoefficients.push_back( Real( 1 ) );
    }
//    cerr << "; SIMPLE UNSAT" << endl;
    return setStatus( UNSAT );
  }

//  cerr << "; write history" << endl;
  // Prepare the history entry
  LAVarHistory &hist = pushed_constraints.back( );
  hist.e = itBound.e;
  hist.v = it;
  hist.bound_type = itBound.bound_type;
  if(itBound.bound_type == bound_u)
  {
    hist.bound = it->u_bound;
    it->u_bound = it_i;
  }
  else
  {
    hist.bound = it->l_bound;
    it->l_bound = it_i;
  }
  // Update the Tableau data if needed
  if( it->isNonbasic( ) )// && *( itBound.delta ) < it->M( ) ) // && *( itBound.delta ) > it->M( ) )
  {
    update( it, *( itBound.delta ) );
  }

//  LAVar *x = it;
//  cerr << "; ASSERTED bound on " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;

//  cerr  << "; NORMAL " << status <<endl;
  return getStatus( );
  //  return check(true);
}

//
// Push the solver one level down
//
void LRASolver::pushBacktrackPoint( )
{
//  cerr << "; push " << pushed_constraints.size( ) << endl;
  // Check if any updates need to be repeated after backtrack
  if( first_update_after_backtrack )
  {
//    cerr << "; re-apply " << pushed_constraints.size( ) << " - " << checks_history.back( ) << endl;
    for( unsigned i = checks_history.back( ); i < pushed_constraints.size( ); i++ )
    {
      LAVar * v = pushed_constraints[i].v;
      if( v != NULL && v->isNonbasic( ) && v->isModelOutOfBounds( ) )
      {
        if( v->isModelOutOfUpperBound( ) )
          update( v, v->U( ) );
        else
          update( v, v->L( ) );
      }
    }
    //          assertBoundOnColumn(pushed_constraints[i].v, pushed_constraints[i].bound, true);
    //        assertLit( pushed_constraints[i].e, false );

//    cerr << "; ";
//    for( unsigned i = 0; i < checks_history.size( ); i++ )
//      cerr << checks_history[i] << " ";
//    cerr << endl;
    //    assert(checks_history.back( ) == pushed_constraints.size( ));
    first_update_after_backtrack = false;
  }

  // Create and push new history step
  LAVarHistory hist;
  hist.e = PTRef_Undef;
  hist.v = NULL;
  pushed_constraints.push_back( hist );

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
    LAVarHistory &hist = pushed_constraints.back( );

    if ( hist.v != NULL )
    {
        if (hist.bound_type == bound_u)
            hist.v->u_bound = hist.bound;
        else
            hist.v->l_bound = hist.bound;
    }

    //TODO: Keep an eye on SAT model crossing the bounds of backtracking
    //  if( status == UNSAT && checks_history.back( ) == pushed_constraints.size( ) )
    if ( checks_history.back( ) == pushed_constraints.size( ) )
    {
//    cerr << "; POP CHECKS " << checks_history.back( ) << endl;
        checks_history.pop_back( );
    }
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
        assert(columns[i] != NULL);
        if (!columns[i]->skip && columns[i]->isNonbasic( ) &&
            columns[i]->isUnbounded( ) && columns[i]->binded_rows.size( ) > 1) {
            LAVar * x = columns[i];

            LAColumn::iterator it = x->binded_rows.begin( );

            assert( it != x->binded_rows.end( ) );

            int basisRow = it->key;
            LAVar * basis = rows[basisRow];

//            printf("; LAVar for column %d is %s and LAVar for the basis is %s\n", i, logic.printTerm(x->e), logic.printTerm(basis->e));
            Real a( *( rows[it->key]->polynomial[it->pos_in_row].coef ) );
            x->binded_rows.getNext( it );

            assert( it != x->binded_rows.end( ) );

//            printf("; Number of rows bound to %s is %d\n", logic.printTerm(basis->e), x->binded_rows.size());
            for (; it != x->binded_rows.end( ); x->binded_rows.getNext( it )) {
                Real ratio( ( *( rows[it->key]->polynomial[it->pos_in_row].coef ) ) / a );
                for (LARow::iterator it2 = basis->polynomial.begin( );
                     it2 != basis->polynomial.end( );
                     basis->polynomial.getNext( it2 )) {
                    LARow::iterator a_it = rows[it->key]->polynomial.find( it2->key );
                    if (a_it == rows[it->key]->polynomial.end( )) {
                        // if it2->key is not in it->key's polynomial we
                        // multiply the coefficient of it2 by it's coef/a
                        Real val(-ratio * (*basis->polynomial.find(it2->key)->coef));
                        Real * c = NULL;
                        if (!numbers_pool.empty( )) {
                            c = numbers_pool.back( );
                            numbers_pool.pop_back( );
                            *c = val;
                        } else {
                            c = new Real(val);
                        }
                        columns[it2->key]->binded_rows.add( it->key, rows[it->key]->polynomial.add( it2->key, columns[it2->key]->binded_rows.free_pos( ), c ) );
                    } else {
                        // if it2->key is in it->key's polynomial
                        *(a_it->coef) -= ( *( basis->polynomial.find( it2->key )->coef ) ) * ratio;
                        if (*( a_it->coef ) == 0) {
                            // The term vanished
                            assert( a_it->coef );
                            // Store removed Real in memory pool
                            numbers_pool.push_back( a_it->coef );
                            if ( it2->key != x->ID( ) )
                                columns[it2->key]->binded_rows.remove( a_it->pos );
                            rows[it->key]->polynomial.remove( a_it );
                        }
                    }
                }
            }

            // Clear removed row
            for (LARow::iterator it2 = basis->polynomial.begin();
                 it2 != basis->polynomial.end();
                 basis->polynomial.getNext(it2))
            {
                if (it2->key != basis->ID()) {
                    columns[it2->key]->unbindRow( basisRow );
                }
                assert( it2->coef );
            }

            // Keep polynomial in x to compute a model later
            assert( x->polynomial.empty( ) );
            swap( basis->polynomial, x->polynomial );
            removed_by_GaussianElimination.push_back( x );
            x->binded_rows.clear( );
            x->skip = true;

            // Replace basisRow slot with the last row in rows vector
            int m = rows.size( ) - 1;
            if (m > basisRow) {
                for (LARow::iterator it2 = rows[m]->polynomial.begin();
                     it2 != rows[m]->polynomial.end();
                     rows[m]->polynomial.getNext(it2))
                {
                    if (it2->key != rows[m]->ID()) {
                        columns[it2->key]->binded_rows.remove( it2->pos );
                        columns[it2->key]->binded_rows.add( basisRow, rows[m]->polynomial.getPos( it2 ) );
                    }
                }
                assert(rows[m] != NULL);
                rows[basisRow] = rows[m];
                rows[m]->setBasic( basisRow );
            }
            basis->setNonbasic( );
            rows.pop_back( );
#ifdef GAUSSIAN_DEBUG
            printf("; Removed the row %s\n", logic.printTerm(basis->e));
            printf("; Removed column %s\n", logic.printTerm(x->e));
            printf("; rows: %d, columns: %d\n", rows.size(), nVars());
#endif
        }
    }
}

//
// updates the model values according to asserted bound
//
void LRASolver::update( LAVar * x, const Delta & v )
{
  // update model value for all basic terms
  const Delta & v_minusM = v - x->M( );
  for( LAColumn::iterator it = x->binded_rows.begin( ); it != x->binded_rows.end( ); x->binded_rows.getNext( it ) )
  {
    LAVar & row = *( rows[it->key] );
    row.incM( *( row.polynomial[it->pos_in_row].coef ) * v_minusM );

    if( static_cast<int> ( row.polynomial.size( ) ) <= config.lra_poly_deduct_size )
      touched_rows.insert( rows[it->key] );

    //TODO: make a separate config value for suggestions
    //TODO: sort the order of suggestion requesting based on metric (Model increase, out-of-bound distance etc)
    //    if( config.lra_theory_propagation == 3 )
    //    {
    //      if( suggestions.empty( ) )
    //        rows[it->key]->getSuggestions( suggestions, id );
    //    }
  }
  x->setM( v );
//  cerr << "; UPDATED nonbasic " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;
}

//
// pivots x and y in solver and does all updates
//
void LRASolver::pivotAndUpdate( LAVar * x, LAVar * y, const Delta & v )
{
//  std::cerr << "; PIVOT AND UPDATE" << *x << " - " << *y << " - " << v << endl;
  assert( x != y );
  assert( x->isBasic( ) );
  assert( y->isNonbasic( ) );

  assert( y->polynomial.empty( ) );
  assert( x->binded_rows.empty( ) );
  assert( x->polynomial.exists( y->ID( ) ) );

  // get Theta (zero if Aij is zero)
  const Real & a = *( x->polynomial.find( y->ID( ) )->coef );
  assert( a != 0 );
  Delta theta = ( v - x->M( ) ) / a;

  // update models of x and y
  x->setM( v );
  y->incM( theta );

  // update model of Basic variables
  for (LAColumn::iterator it = y->binded_rows.begin( ); it != y->binded_rows.end( ); y->binded_rows.getNext( it ))
  {

    if (rows[it->key] != x)
    {
      LAVar & row = *( rows[it->key] );
      row.incM( *( row.polynomial[it->pos_in_row].coef ) * theta );
      if (static_cast<int> ( row.polynomial.size( ) ) <= config.lra_poly_deduct_size)
        touched_rows.insert( rows[it->key] );
    }
  }
  // pivoting x and y

#if FAST_RATIONALS
  const Real inverse = -FastRational_inverse( a );
#else
  const Real inverse = -1 / a;
#endif

  // more debug
  if (a == 1) {
      assert(inverse == -1);
  }

  // NEW VARIANT OF PIVOTING

  //  for( LARow::iterator it = x->polynomial.begin( ); it != x->polynomial.end( ); x->polynomial.getNext( it ) )
  //  {
  //    // first inverse the coeff of the pivoting row
  //    *( it->coef ) *= inverse;
  //
  //    assert( it->key != y->ID( ) || ( *( x->polynomial.find( y->ID( ) )->coef ) == -1 ) );
  //
  //    const Real &b = *( it->coef );
  //    assert( b != 0 );
  //
  //    for( LARow::iterator it2 = y->binded_rows.begin( ); it2 != y->binded_rows.end( ); y->binded_rows.getNext( it2 ) )
  //    {
  //      // skip the pivoting column and row for now
  //      if( it2->key == x->basicID( ) || it->key == y->ID( ) )
  //        continue;
  //      else
  //      {
  //        assert( it->key != y->ID( ) );
  //        assert( it2->key != x->basicID( ) );
  //
  //        const Real &a = *( it2->coef );
  //        assert( a != 0 );
  //
  //        // add to existing coefficient
  //        if( rows[it2->key]->polynomial.exists( it->key ) )
  //        //        if( columns[it->key]->binded_rows.exists( it2->key ) )
  //        {
  ////          if( columns[it->key]->binded_rows.size( ) > rows[it2->key]->polynomial.size( ) )
  ////            cout << 1 ;
  ////          else
  ////            cout << 0;
  ////            cout << columns[it->key]->binded_rows.size( ) << " vs " << rows[it2->key]->polynomial.size( ) << endl;
  ////          LARow::iterator c_it = columns[it->key]->binded_rows.findfast( it2->key );
  ////          assert (c_it!=columns[it->key]->binded_rows.end());
  ////          Real * p_c = c_it->coef;
  ////          *( p_c ) += b * a;
  ////          // delete element from P_i if it become 0
  ////          if( *( p_c ) == 0 )
  ////          {
  ////            // Save Real in pool
  ////            numbers_pool.push_back( p_c );
  ////            // Mark out the value from column and row
  ////            rows[it2->key]->polynomial.remove( c_it->pos );
  ////            assert( it->key != y->ID( ) );
  ////            columns[it->key]->binded_rows.remove( c_it );
  ////          }
  //
  ////
  //          LARow::iterator c_it = rows[it2->key]->polynomial.findfast( it->key );
  //          assert (c_it!=rows[it2->key]->polynomial.end());
  //          Real * p_c = c_it->coef;
  //          *( p_c ) += b * a;
  //          // delete element from P_i if it become 0
  //          if( *( p_c ) == 0 )
  //          {
  //            // Save Real in pool
  //            numbers_pool.push_back( p_c );
  //            // Mark out the value from column and row
  ////            assert( it->key != y->ID( ) );
  //            columns[it->key]->binded_rows.remove( c_it->pos );
  //            rows[it2->key]->polynomial.remove( c_it);
  //          }
  //
  //        }
  //        // or insert new element to P_i
  //        else
  //        {
  //          // handle reals via memory pool
  //          Real * p_c = NULL;
  //          if( !numbers_pool.empty( ) )
  //          {
  //            p_c = numbers_pool.back( );
  //            numbers_pool.pop_back( );
  //            *p_c = a * b;
  //          }
  //          else
  //          {
  //            p_c = new Real( a * b );
  //          }
  //          columns[it->key]->binded_rows.add( it2->key, rows[it2->key]->polynomial.add( it->key, columns[it->key]->binded_rows.free_pos( ), p_c ), p_c );
  //        }
  //      }
  //
  //      // mark the affected row (for deductions)
  //      if( static_cast<int> ( rows[it2->key]->polynomial.size( ) ) <= config.lra_poly_deduct_size )
  //        touched_rows.insert( rows[it2->key] );
  //    }
  //  }
  //
  //  //clean the position y in all the rows
  //  for( LARow::iterator it2 = y->binded_rows.begin( ); it2 != y->binded_rows.end( ); y->binded_rows.getNext( it2 ) )
  //  {
  //    if( it2->key != x->basicID( ) )
  //    {
  //      numbers_pool.push_back( it2->coef );
  //      assert( rows[it2->key]->polynomial.find( y->ID() ) != rows[it2->key]->polynomial.end( ) );
  //      LARow::iterator it = rows[it2->key]->polynomial.find( y->ID() );
  //      assert( rows[it2->key]->polynomial[it2->pos].key == y->ID() );
  //      rows[it2->key]->polynomial.remove( it2->pos );
  //    }
  //  }

  // OLD PIVOTING
  // first change the attribute values for x polynomial
  for( LARow::iterator it = x->polynomial.begin( ); it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    *( it->coef ) *= inverse;

  // value of a_y should become -1
  assert( *( x->polynomial.find( y->ID( ) )->coef ) == -1 );

  // now change the attribute values for all rows where y was presented
  for( LAColumn::iterator it = y->binded_rows.begin( ); it != y->binded_rows.end( ); y->binded_rows.getNext( it ) )
  {
    // check that the modified row is not x (it was changed already)
    if( rows[it->key] != x )
    {
      LAVar & row = *( rows[it->key] );

      assert( *( row.polynomial[it->pos_in_row].coef ) != 0 );

      // copy a to the new Real variable (use memory pool)
      //TODO: make a function for the code below
      Real * p_a = NULL;
      if( !numbers_pool.empty( ) )
      {
        p_a = numbers_pool.back( );
        numbers_pool.pop_back( );
        *p_a = *( row.polynomial[it->pos_in_row].coef );
      }
      else
      {
        p_a = new Real( *( row.polynomial[it->pos_in_row].coef ) );
      }

      const Real& a = *( p_a );

      // P_i = P_i + a_y * P_x (iterate over all elements of P_x)
      for( LARow::iterator it2 = x->polynomial.begin( ); it2 != x->polynomial.end( ); x->polynomial.getNext( it2 ) )
      {
        LAVar & col = *( columns[it2->key] );

        const Real &b = *( it2->coef );
        assert( b != 0 );
        // insert new element to P_i
        if( !row.polynomial.exists( it2->key ) )
        {
          // handle reals via memory pool
          Real * p_c = NULL;
          if( !numbers_pool.empty( ) )
          {
            p_c = numbers_pool.back( );
            numbers_pool.pop_back( );
            *p_c = a * b;
          }
          else
          {
            p_c = new Real( a * b );
          }
          col.binded_rows.add( it->key, row.polynomial.add( it2->key, col.binded_rows.free_pos( ), p_c ) );
        }
        // or add to existing
        else
        {
          LARow::iterator a_it = row.polynomial.find( it2->key );
          assert( a_it != row.polynomial.end( ) );
          *( a_it->coef ) += b * a;
          if( *( a_it->coef ) == 0 )
          {
            // delete element from P_i if it become 0
            assert( a_it->coef );

            // Save Real in pool
            numbers_pool.push_back( a_it->coef );

            // Mark out the value from column and row
            if( it2->key != y->ID( ) )
              col.binded_rows.remove( a_it->pos );
            row.polynomial.remove( a_it );
          }
        }
      }
      numbers_pool.push_back( p_a );

      assert( ( row.polynomial.find( y->ID( ) ) == row.polynomial.end( ) ) );

      // mark the affected row (for deductions)
      if( static_cast<int> ( row.polynomial.size( ) ) <= config.lra_poly_deduct_size )
        touched_rows.insert( rows[it->key] );
    }
  }

  // swap x and y (basicID, polynomial, bindings)
  swap( x->polynomial, y->polynomial );
  assert( x->polynomial.empty( ) );
  assert( !y->polynomial.empty( ) );
  y->setBasic( x->basicID( ) );
  x->setNonbasic( );
  assert(y != NULL);
  rows[y->basicID( )] = y;

  assert( y->polynomial.find( x->ID( ) ) != y->polynomial.end( ) );
  assert( y->polynomial.find( x->ID( ) )->pos >= 0 );
  assert( y->polynomial.find( x->ID( ) ) != y->polynomial.end( ) );
  const LARow::iterator tmp_it = y->polynomial.find( x->ID( ) );
  tmp_it->pos = x->binded_rows.free_pos( );
  x->binded_rows.add( y->basicID( ), y->polynomial.getPos( tmp_it ) );
  y->binded_rows.clear( );

  if( static_cast<int> ( y->polynomial.size( ) ) <= config.lra_poly_deduct_size )
    touched_rows.insert( y );
  touched_rows.erase( x );

  assert( x->polynomial.size( ) == 0 );
  assert( y->polynomial.size( ) > 0 );
  assert( x->binded_rows.size( ) > 0 );
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
  switch( status )
  {
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
void LRASolver::getConflictingBounds( LAVar * x, vec<PTRef> & dst )
{
  LAVar * y;
  if( x->M( ) < x->L( ) )
  {
    // add all bounds for polynomial elements, which limit lower bound
    LARow::iterator it = x->polynomial.begin( );
    for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      const Real a = *(it->coef);
      y = columns[it->key];
      assert( a != 0 );
      if( x == y )
      {
        assert( y->all_bounds[y->l_bound].e != PTRef_Undef );

        dst.push( y->all_bounds[y->l_bound].e );
        explanationCoefficients.push_back( Real( 1 ) );
      }
      else if( a < 0 )
      {
        assert( !y->L( ).isInf( ) );
        assert( y->all_bounds[y->l_bound].e != PTRef_Undef );

        dst.push( y->all_bounds[y->l_bound].e );
        explanationCoefficients.push_back( -a );
      }
      else
      {
        assert( !y->U( ).isInf( ) );
        assert( y->all_bounds[y->u_bound].e != PTRef_Undef );

        dst.push( y->all_bounds[y->u_bound].e );
        explanationCoefficients.push_back( a );
      }
    }
  }
  if( x->M( ) > x->U( ) )
  {
    // add all bounds for polynomial elements, which limit upper bound
    LARow::iterator it = x->polynomial.begin( );
    for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      const Real a = *(it->coef);
      y = columns[it->key];
      assert( a != 0 );
      if( x == y )
      {
        assert( y->all_bounds[y->u_bound].e != PTRef_Undef );

        dst.push( y->all_bounds[y->u_bound].e );
        explanationCoefficients.push_back( Real( 1 ) );
      }
      else if( a > 0 )
      {
        assert( !y->L( ).isInf( ) );
        assert( y->all_bounds[y->l_bound].e != PTRef_Undef );

        dst.push( y->all_bounds[y->l_bound].e );
        explanationCoefficients.push_back( a );
      }
      else
      {
        assert( !y->U( ).isInf( ) );
        assert( y->all_bounds[y->u_bound].e != PTRef_Undef );

        dst.push( y->all_bounds[y->u_bound].e );
        explanationCoefficients.push_back( -a );
      }
    }
  }

  assert( dst.size( ) == x->polynomial.size( ) );

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

//
// Compute the current bounds for each row and tries to deduce something useful
//
void LRASolver::refineBounds( )
{

  // Check if polynomial deduction is enabled
  if( config.lra_poly_deduct_size == 0 )
    return;

  // iterate over all rows affected in the current check
  for( set<LAVar *>::const_iterator t_it = touched_rows.begin( ); t_it != touched_rows.end( ); ++t_it )
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
}

//
// Prints the current state of the solver (terms, bounds, tableau)
//
void LRASolver::print( ostream & out )
{
  out << "Bounds:" << endl;

  // print bounds array size
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->all_bounds.size( ) << "\t";
  out << endl;

  // print the upper bounds
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->U( ) << "\t";
  out << endl;

  // print the lower bounds
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->L( ) << "\t";
  out << endl;

  // print current model values
  out << "Var:" << endl;
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
  {
    out << ( *it ) << "\t";
  }
  out << endl;

  // print current model values
  out << "Model:" << endl;
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->M( ) << "\t";
  out << endl;

  // print the terms IDs
  out << "Tableau:" << endl;
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->ID( ) << "\t";
  out << endl;

  // print the Basic/Nonbasic status of terms
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( ( *it )->isBasic( ) ? "B" : "N" ) << "\t";
  out << endl;

  // print the tableau cells (zeros are skipped)
  // iterate over Tableau rows
  for( unsigned i = 0; i < rows.size( ); ++i )
  {
    for( VectorLAVar::iterator it2 = columns.begin( ); it2 != columns.end( ); ++it2 )
    {
      if( rows[i]->polynomial.find( ( *it2 )->ID( ) ) != rows[i]->polynomial.end( ) )
        out << *( rows[i]->polynomial.find( ( *it2 )->ID( ) )->coef );
      out << "\t";
    }
    out << endl;
  }
}

//
// Detect the appropriate value for symbolic delta and dumps the model into Egraph
//
void LRASolver::computeModel( )
{
  assert( status == SAT );

  Real minDelta( 0 );
  Real maxDelta( 0 );
  Real curDelta( 0 );
  Delta curBound( Delta::ZERO );
  LAVar * col;

  //
  // For all columns check the min/max value for delta
  // Note, it should be always that min > 0 and max < 0
  //
  for( unsigned i = 0; i < columns.size( ); ++i )
  {
    if( columns[i]->skip )
      continue;
#ifdef GAUSSIAN_DEBUG
    printf("computing model for %s (%d)\n", logic.printTerm(columns[i]->e), columns[i]->e.x);
    cerr << "It's M is " << columns[i]->M() << '\n';
#endif
    col = columns[i];
    assert( !col->isModelOutOfBounds( ) );

    curDelta = 0;
    curBound = Delta( Delta::ZERO );

    // Check if the lower bound can be used and at least one of delta and real parts are not 0
    if( !col->L( ).isInf( )
     && ( col->L( ).D( ) != 0 || col->M( ).D( ) != 0 )
     && ( col->L( ).R( ) != 0 || col->M( ).R( ) != 0 ) )
    {
      curBound = col->L( ) - col->M( );

      // if denominator is >0 then use delta for min
      if( curBound.D( ) > 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
          minDelta = curDelta;
      }
      // if denominator is <0 than use delta for max
      else if( curBound.D( ) < 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
          maxDelta = curDelta;
      }
    }
    // Check if the upper bound can be used and at least one of delta and real parts are not 0
    if( !col->U( ).isInf( )
     && ( col->U( ).D( ) != 0 || col->M( ).D( ) != 0 ) 
     && ( col->U( ).R( ) != 0 || col->M( ).R( ) != 0 ) )
    {
      curBound = col->M( ) - col->U( );

      // if denominator is >0 than use delta for min
      if( curBound.D( ) > 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
          minDelta = curDelta;
      }
      // if denominator is <0 than use delta for max
      else if( curBound.D( ) < 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
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
      columns[i]->computeModel( curDelta );

  // Compute the value for each variable deleted by Gaussian elimination
  while( !removed_by_GaussianElimination.empty( ) )
  {
    LAVar * x = removed_by_GaussianElimination.back( );
    Real div = 0;
    Delta v_delta(0);

    for( LARow::iterator it = x->polynomial.begin( ); it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      col = columns[it->key];
      if( col != x ) {
            v_delta += *(it->coef) * col->M();
      }
      else {
        div -= *( it->coef );
      }
    }
    assert( div != 0 );
    x->setM(v_delta/div);
//    cout << "value of " << logic.printTerm(x->e) << " is " << x->M() << endl;

    removed_by_GaussianElimination.pop_back( );
  }
}

// Fill the vector with the vars removed due to not having bounds
const void LRASolver::getRemoved(vec<PTRef>& removed) const
{
    for (int i = 0; i < removed_by_GaussianElimination.size(); i++)
        removed.push(removed_by_GaussianElimination[i]->e);
}

//
//
//
void LRASolver::addVarToRow( LAVar* s, LAVar* x, Real * p_v )
{
    if (x->isNonbasic()) {
        LARow::iterator p_it = s->polynomial.find(x->ID());
        if (p_it != s->polynomial.end()) {
            *(p_it->coef) += *p_v;
            if (*(p_it->coef) == 0) {
                numbers_pool.push_back(p_it->coef);
                x->binded_rows.remove(p_it->pos);
                s->polynomial.remove(p_it);
            }
        }
        else {
          x->binded_rows.add( s->basicID( ), s->polynomial.add( x->ID( ), x->binded_rows.free_pos( ), p_v ) );
        }
    }
    else {
        LARow::iterator it = x->polynomial.begin( );
        for (; it != x->polynomial.end(); x->polynomial.getNext(it)) {
            if (x->ID( ) == it->key)
                continue;

            assert(columns[it->key]->isNonbasic());

            Real * tmp_r;

            if (!numbers_pool.empty()) {
                tmp_r = numbers_pool.back();
                numbers_pool.pop_back();
                *tmp_r = Real( *(it->coef) * (*p_v));
            }
            else {
                tmp_r = new Real(*( it->coef ) * ( *p_v ));
            }
            LARow::iterator p_it = s->polynomial.find(it->key);
            if (p_it != s->polynomial.end()) {
                *(p_it->coef) += *tmp_r;
                numbers_pool.push_back(tmp_r);
                if (*(p_it->coef) == 0) {
                    numbers_pool.push_back(p_it->coef);
                    columns[it->key]->binded_rows.remove(p_it->pos);
                    s->polynomial.remove(p_it);
                }
            }
            else {
                columns[it->key]->binded_rows.add( s->basicID( ), s->polynomial.add( it->key, columns[it->key]->binded_rows.free_pos( ), tmp_r ) );
            }
        }
        numbers_pool.push_back( p_v );
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
//        cerr << "; getting value for term " << logic.printTerm(tr) << " (" << *ptermToLavar[id] << ")" << endl;
        const Delta v = ptermToLavar[id]->M();
        for (int i = 0; i < removed_by_GaussianElimination.size(); i++) {
            if (tr == removed_by_GaussianElimination[i]->e)
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
  // Remove lavarStore
  delete lavarStore;
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
        if(usingFactor())
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
            if(strength_factor < 0 || strength_factor >= 1)
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
        else if(usingStrong())
        {
            args.push(logic.mkConst("0"));
            args.push(interpolant.toPTRef());
        }
        else if(usingWeak())
        {
            args.push(logic.mkConst("0"));
            args.push(interpolant_dual.toPTRef());
        }
        else
        {
            opensmt_error("Error: interpolation algorithm not set for LRA.");
        }

        char* msg;
        if(!usingWeak())
        {
            if(delta_flag)
                itp = logic.mkRealLt(args, &msg);
            else
                itp = logic.mkRealLeq(args, &msg);
        }
        else
        {
            if(delta_flag)
                itp = logic.mkRealLt(args, &msg);
            else
                itp = logic.mkRealLeq(args, &msg);
            itp = logic.mkNot(itp);
        }
    }

    if(verbose() > 1)
    {
        cerr << "; LRA Itp: " << logic.printTerm(itp) << endl;
    }

    return itp;
}

#endif

