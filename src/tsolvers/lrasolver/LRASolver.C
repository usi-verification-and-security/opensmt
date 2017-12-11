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

int
LRAModel::addVar(LVRef v)
{
    if (has_model.has(v))
        return n_vars_with_model;

    while (int_model.size() <= lva[v].ID()) {
        int_model.push();
        int_lbounds.push();
        int_ubounds.push();
    }
    has_model.insert(v, true);
    write(v, Delta());
    int_lbounds[lva[v].ID()].push({ bs.minusInf(), 0 });
    int_ubounds[lva[v].ID()].push({ bs.plusInf(), 0 });
    return ++n_vars_with_model;
}

void
LRAModel::write(const LVRef &v, const Delta& val)
{
    if ((int_model[lva[v].ID()].size() == 0) || (int_model[lva[v].ID()].last().dl != decisionLevel())) {
        int_model[lva[v].ID()].push();
    }
    int_model[lva[v].ID()].last().d = val;
}

void
LRAModel::pushBound(const LABoundRef) {
}


void
LRAModel::popBound(const LABoundRef br)
{
    LABound& b = bs[br];
    LVRef vr = b.getLVRef();
    LABoundRef latest_bound = LABoundRef_Undef;
    if (b.getType() == bound_u) {
        int_ubounds[lva[vr].ID()].pop();
        latest_bound = int_ubounds[lva[vr].ID()].last().br;
        lva[vr].setUbound(bs[latest_bound].getIdx());
    } else {
        int_lbounds[lva[vr].ID()].pop();
        latest_bound = int_lbounds[lva[vr].ID()].last().br;
        lva[vr].setLbound(bs[latest_bound].getIdx());
    }
}

LRASolver::LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d)
    : logic(l)
    , bindedRowsStore(l, lva, bra)
    , pa(pta)
    , polyStore(lva, pa, bindedRowsStore, l)
    , TSolver((SolverId)descr_lra_solver, (const char*)descr_lra_solver, c, d)
    , delta(Delta::ZERO)
    , bland_threshold(1000)
    , lavarStore(lva)
    , boundStore(ba, bla, lva, lavarStore, l)
    , model(LATrace_lim, LABound_trace_lim, lva, boundStore)
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

const Delta& LRASolver::Ub(LVRef v) const
{
    const LAVar& va = lva[v];
    const LABoundList &bl = bla[va.getBounds()];
    return ba[bl[va.ubound()]].getValue();
}

const Delta& LRASolver::Lb(LVRef v) const
{
    const LAVar& va = lva[v];
    const LABoundList &bl = bla[va.getBounds()];
    return ba[bl[va.lbound()]].getValue();
}

//
// The model system
//
bool LRASolver::isModelOutOfBounds(LVRef v) const
{
    return ( (model.read(v) > Ub(v)) || (model.read(v) < Lb(v)) );
}

bool LRASolver::isModelOutOfUpperBound(LVRef v) const
{
    return ( model.read(v)> Ub(v) );
}

bool LRASolver::isModelOutOfLowerBound(LVRef v) const
{
    return ( model.read(v) < Lb(v) );
}


const Delta LRASolver::overBound(LVRef v) const
{
    assert( isModelOutOfBounds(v) );
    if (isModelOutOfUpperBound(v))
    {
        return ( Delta(model.read(v) - Ub(v)) );
    }
    else if ( isModelOutOfLowerBound(v) )
    {
        return ( Delta(Lb(v) - model.read(v)) );
    }
    assert (false);
}


bool LRASolver::isModelInteger(LVRef v) const
{
    return !( model.read(v).hasDelta() || !model.read(v).R().den_is_unit() );
}

bool LRASolver::isEquality(LVRef v) const
{
    return lva[v].lbound()+1 == lva[v].ubound() && !Lb(v).isInf() && !Ub(v).isInf() && Lb(v) == Ub(v);
}

bool LRASolver::isUnbounded(LVRef v) const
{
    return lva[v].getBounds() == LABoundListRef_Undef;
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
    Pterm& leq = logic.getPterm(leq_tr);
    PTRef const_tr = leq[0];
    PTRef var_tr = leq[1];

    BoundT bound_t = logic.isNegated(var_tr) ? bound_u : bound_l;
    boundStore.addBound(getLAVar_single(var_tr), leq_tr, leq.getId(), logic.getRealConst(const_tr), bound_t);
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
    if (ptermToLavar.size() > Idx(id) && ptermToLavar[Idx(id)] != LVRef_Undef)
        return true;
    return false;
}

LVRef LRASolver::getLAVar_single(PTRef expr_in) {
    PTRef expr = logic.isNegated(expr_in) ? logic.mkRealNeg(expr_in) : expr_in;
    LVRef x;

    PTId id_pos = logic.getPterm(expr).getId();
    PTId id_neg = logic.getPterm(logic.mkRealNeg(expr)).getId();
    int max_id = max(Idx(id_pos), Idx(id_neg));

    if (max_id >= ptermToLavar.size())
        ptermToLavar.growTo(max_id+1, LVRef_Undef);

    assert(ptermToLavar[Idx(id_pos)] == ptermToLavar[Idx(id_neg)]);

    if (ptermToLavar[Idx(id_pos)] == LVRef_Undef) {
        x = lavarStore.getNewVar(expr);
        ptermToLavar[Idx(id_pos)] = x;
        ptermToLavar[Idx(id_neg)] = x;

        model.addVar(x);
        vec<PolyTermRef> tmp;
        lva[x].setPolyRef(polyStore.makePoly(x, tmp));
        lva[x].setBindedRowsRef(bra.alloc());
    }
    else
        x = ptermToLavar[Idx(id_pos)];

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
    if (hasVar(term))
        return ptermToLavar[Idx(logic.getPterm(term).getId())];
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
            PolyTermRef ptr = pta.alloc(*c_r, nb);
            sum_terms.push(ptr);
        }
        setBasic(x);
        if (lva[x].getRowId() == -1) {
            lva[x].setRowId(rows.size());
            rows.push(x);
        }
        PolyRef pr  = pa.alloc(sum_terms);
        lva[x].setPolyRef(pr);

        for (int i = 0; i < sum_terms.size(); i++) {
            LVRef v = pta[sum_terms[i]].var;
            assert(v != x);
            bindedRowsStore.add(x, i, v);
        }
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

    int idx = Idx(leq_t.getId());
    for (int i = leqToLavar.size(); i <= idx; i++)
        leqToLavar.push(LVRef_Undef);
    leqToLavar[idx] = v;

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

    printf("Check\n");
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
                    if (x == LVRef_Undef || (pa[lva[x].getPolyRef()].size() > pa[lva[it].getPolyRef()].size()))
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

        Real * a;
        LVRef y = LVRef_Undef;
        LVRef y_found = y;

        // Model doesn't fit the lower bound
        if (model.read(x) < Lb(x)) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the breaking of the bound
            for (int i = 0; i < polyStore.getPoly(x).size(); i++) {
                y = pta[polyStore.getPoly(x)[i]].var;
                assert(!lva[y].isBasic() );
                a = &pta[polyStore.getPoly(x)[i]].coef;
                if (x == y)
                    continue;

                assert(a != 0);
                const bool & a_is_pos = ( *a ) > 0;
                if ((a_is_pos && model.read(y) < Ub(y)) || (!a_is_pos && model.read(y) > Lb(y))) {
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
        } else if (model.read(x) > Ub(x)) {
            // For the Bland rule
            int curr_var_id_y = max_var_id;
            // look for nonbasic terms to fix the unbounding
            for (int i = 0; i < polyStore.getPoly(x).size(); i++) {
                y = pta[polyStore.getPoly(x)[i]].var;
                if (x == y)
                    continue;
//                cerr << "; " << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                assert( !lva[y].isBasic() );
                a = &pta[getPoly(x)[i]].coef;
                assert(a != 0);
                const bool & a_is_pos = (*a) > 0;
                if ((!a_is_pos && model.read(y) < Ub(y)) || (a_is_pos && model.read(y) > Lb(y))) {
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
    printf("check ended.  Status is %s\n", getStatus() ? "sat" : "unsat");
    return getStatus();
}

//
// Push the constraint into the solver and increase the level
//
bool LRASolver::assertLit( PtAsgn asgn, bool reason )
{
    ( void )reason;

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

    printf("Asserting %s%s\n", (asgn.sgn == l_False ? "not " : ""), logic.printTerm(asgn.tr));
    bool is_reason = false;

    Pterm& t = logic.getPterm(asgn.tr);

    // skip if it was deduced by the solver itself with the same polarity
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].polarity == asgn.sgn && deduced[t.getVar()].deducedBy == id) {
        getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
        return getStatus( );
    }
    if (deduced[t.getVar()] != l_Undef && deduced[t.getVar()].deducedBy == id)
        is_reason = true; // This is a conflict!

    setPolarity(asgn.tr, asgn.sgn);

    LVRef it = leqToLavar[Idx(t.getId())];

    // Constraint to push was not found in local storage. Most likely it was not read properly before
    if ( it == LVRef_Undef ) {
        std::cout << logic.printTerm(asgn.tr) << "\n";
        throw "Unexpected push";
    }

    assert( !isUnbounded(it) );

    LABoundRefPair p = boundStore.getBoundRefPair(asgn.tr);
    LABoundRef bound_ref = asgn.sgn == l_False ? p.neg : p.pos;
    LABound& bound = ba[bound_ref];
    BoundIndex it_i = bound.getIdx();

    if (assertBoundOnVar( it, it_i ))
    {
        model.pushBound(bound_ref);
        LABound_trace.push(bound_ref);
        if (bound.getType() == bound_l)
            lva[it].setLbound(it_i);
        else
            lva[it].setUbound(it_i);


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

bool LRASolver::assertBoundOnVar( LVRef it, BoundIndex it_i )
{
    // No check whether the bounds are consistent for the polynomials.  This is done later with Simplex.

    assert( status == SAT );
    assert( it != LVRef_Undef );
    assert( !isUnbounded(it) );
    const LABoundRef itBound_ref = getBound(it, it_i);
    const LABound &itBound = ba[itBound_ref];

//  cerr << "; ASSERTING bound on " << *it << endl;

    // Check is simple SAT can be given
    if (((itBound.getType() == bound_u) && !(it_i < lva[it].ubound()))
        || ((itBound.getType() == bound_l) && !(it_i > lva[it].lbound())))
    {
//      cerr << "; SIMPLE SAT" << endl;
        return getStatus();
    }
    // Check if simple UNSAT can be given.  The last check checks that this is not actually about asserting equality.
    if (((itBound.getType() == bound_l) && ( it_i > lva[it].ubound() && itBound.getValue() != ba[bla[lva[it].getBounds()][lva[it].ubound()]].getValue()))
     || ((itBound.getType() == bound_u) && ( it_i < lva[it].lbound() && itBound.getValue() != ba[bla[lva[it].getBounds()][lva[it].lbound()]].getValue())))
    {
        explanation.clear();
        explanationCoefficients.clear();

        if (itBound.getType() == bound_u)
        {
            PTRef tr = ba[bla[lva[it].getBounds()][lva[it].lbound()]].getPTRef();
            explanation.push(PtAsgn(tr, getPolarity(tr)));
            explanationCoefficients.push_back( Real( 1 ) );
        }
        else if (itBound.getType() == bound_l)
        {
            PTRef tr = ba[bla[lva[it].getBounds()][lva[it].ubound()]].getPTRef();
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
    LATrace_lim.push(LATrace.size());
    LABound_trace_lim.push(LABound_trace.size());
//      cerr << "; re-apply " << pushed_constraints.size( ) << " - " << checks_history.back( ) << endl;

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

    for (int i = LATrace_lim.last(); i < LATrace.size(); i++) {
        LVRef var = LATrace[i];
        popModel(var);
    }
    LATrace.shrink(LATrace.size() - LATrace_lim.last());
    LATrace_lim.pop();

    for (int i = LABound_trace_lim.last(); i < LABound_trace.size(); i++) {
        popBound(LABound_trace[i]);
        printf("retracting %s%s\n", (ba[LABound_trace[i]].getSign() == l_False ? "not " : ""), logic.printTerm(ba[LABound_trace[i]].getPTRef()));
    }
    LABound_trace.shrink(LABound_trace.size() - LABound_trace_lim.last());
    LABound_trace_lim.pop();

    first_update_after_backtrack = true;

    setStatus(SAT);
    TSolver::popBacktrackPoint();
}

// Remove row corresponding to v.  Assumes that the variables appearing in the row have already updated their
// occurrence lists correspondingly.
void LRASolver::removeRow(LVRef v)
{
    int v_row = lva[v].getRowId();
    // Replace basisRow slot with the last row in rows vector
    int m = rows.size() - 1;
    if (m > v_row) {
        assert(rows[m] != LVRef_Undef);
        rows[v_row] = rows[m];
        lva[rows[m]].setBasic();
        lva[rows[m]].setRowId(v_row);
    }
    lva[v].setNonbasic();
    rows.pop();
}

void LRASolver::removeCol(LVRef v)
{
    int v_col = lva[v].getColId();
    if (v_col == -1)
        return; // Already removed

    // Replace v_col slot with the last column in columns vector
    int m = columns.size() - 1;
    if (m > v_col) {
        lva[columns[m]].setColId(v_col);
        columns[v_col] = columns[m];
        lva[v].setColId(-1);
    }
    columns.pop();
}

vec<PTRef> *LRASolver::solveForVar(LVRef poly_var, LVRef var) {
    Poly &p = polyStore.getPoly(poly_var);
    int pos;
    for (pos = 0; pos < p.size(); pos++) {
        if (pta[p[pos]].var == var)
            break;
    }
    assert(pos < p.size());
    Real a(pta[p[pos]].coef);
    vec<PTRef> *gaussian_eq = new vec<PTRef>();
    gaussian_eq->push(logic.mkRealTimes(lva[poly_var].getPTRef(), logic.mkConst(a.inverse())));
    for (int j = 0; j < p.size(); j++) {
        if (j == pos) continue;
        PolyTerm &pt = pta[p[j]];
        gaussian_eq->push(logic.mkRealTimes(lva[pt.var].getPTRef(), logic.mkConst(pt.coef * (-a.inverse()))));
    }
    return gaussian_eq;
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

        if (!lva[x].skip() && isUnbounded(x) && bra[lva[x].getBindedRowsRef()].size() == 0) {
            ; // No action, will be removed
        }
        if (!lva[x].skip() && isUnbounded(x) && bra[lva[x].getBindedRowsRef()].size() == 1)
        {
            // The corresponding row can always be satisfied by picking a value for x
            elim_cols.push(x);
            LVRef my_row = bra[lva[x].getBindedRowsRef()][0].var;
            // Update Polynomials:
            //  (1) Remove refs of all poly's variables on the poly
            Poly& p = polyStore.getPoly(my_row);
            for (int j = 0; j < p.size(); j++) {
                LVRef var = pta[p[j]].var;
                bindedRowsStore.remove(my_row, var);
//                bra[lva[var].getBindedRowsRef()].remove(my_row);
                if (bra[lva[var].getBindedRowsRef()].size() == 0) {
                    bra.free(lva[var].getBindedRowsRef());
                    elim_cols.push(var);
                    vec<PTRef> *gauss_eq = solveForVar(my_row, var);
                    removed_by_GaussianElimination.insert(lva[var].getPTRef(), gauss_eq);
                }
            }
            //  (2) remove the polynomial corresponding to my_row
            polyStore.remove(my_row);
            removeRow(my_row);
        }

        else if (!lva[x].skip() && isUnbounded(x) && bra[lva[x].getBindedRowsRef()].size() >= 2)
        {
            BindedRow& row = bra[lva[x].getBindedRowsRef()][0];
            LVRef basis = row.var;
            int pos = row.pos;

//            printf("; LAVar for column %d is %s and LAVar for the basis is %s\n", i, logic.printTerm(x->e), logic.printTerm(basis->e));
            Real a(pta[polyStore.getPoly(basis)[pos]].coef);

//            printf("; Number of rows bound to %s is %d\n", logic.printTerm(basis->e), x->binded_rows.size());
            for (int j = 1; j < bra[lva[x].getBindedRowsRef()].size(); j++) {
                LVRef it_var = bra[lva[x].getBindedRowsRef()][j].var;
                int   it_pos = bra[lva[x].getBindedRowsRef()][j].pos;
                opensmt::Real ratio(pta[polyStore.getPoly(it_var)[pos]].coef / a);
                for (int k = 0; k < pa[lva[basis].getPolyRef()].size(); k++) {
                    LVRef poly_var = pta[polyStore.getPoly(basis)[k]].var;
                    opensmt::Real tmp(ratio*(pta[polyStore.getPoly(basis).find(poly_var)].coef)); // XXX or negated?
                    int pos = polyStore.add(it_var, poly_var, tmp);
                    if (pos != -1) {
                        assert(basis != poly_var);
                        bindedRowsStore.add(poly_var, pos, basis);
                    }
                }
            }

            // Clear removed row
            for (int j = 0; j < pa[lva[basis].getPolyRef()].size(); j++) {
                PolyTerm &pt = pta[polyStore.getPoly(basis)[j]];
                if (pt.var != basis) {
                    bindedRowsStore.remove(basis, pt.var);
//                    bra[lva[pt.var].getBindedRowsRef()].remove(basis);
                }
            }

            // Keep polynomial in x to compute a model later
            // Do this by solving basis for x, and constructing a new expression which is equal to x.  Save this as
            // a vector of PTRefs.
            removed_by_GaussianElimination.insert(lva[x].getPTRef(), solveForVar(basis, x));
            lva[basis].setPolyRef(PolyRef_Undef);
            bra[lva[x].getBindedRowsRef()].clear();

            removeRow(basis);

#ifdef GAUSSIAN_DEBUG
            printf("; Removed the row %s\n", logic.printTerm(LVA[basis].e));
            printf("; Removed column %s\n", logic.printTerm(LVA[x].e));
            printf("; rows: %d, columns: %d\n", rows.size(), nVars());
#endif
        }
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
    const Delta v_minusM = v - model.read(x);
    for (int i = 0; i < bra[lva[x].getBindedRowsRef()].size(); i++) {
        LVRef row = bra[lva[x].getBindedRowsRef()][i].var;
        int pos = bra[lva[x].getBindedRowsRef()][i].pos;
        model.write(row, model.read(row) + pta[pa[lva[row].getPolyRef()][pos]].coef * v_minusM);

        //TODO: make a separate config value for suggestions
        //TODO: sort the order of suggestion requesting based on metric (Model increase, out-of-bound distance etc)
        //    if( config.lra_theory_propagation == 3 )
        //    {
        //      if( suggestions.empty( ) )
        //        rows[it->key]->getSuggestions( suggestions, id );
        //    }
    }
    model.write(x, v);
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

    assert( pa[lva[bv].getPolyRef()].has(nv) );

    printf("Basic vector %s = %s will be solved for var %s\n", lva.printVar(bv), polyStore.printPoly(lva[bv].getPolyRef()), lva.printVar(nv));

    // get Theta (zero if Aij is zero)
    const Real & a = pta[pa[lva[bv].getPolyRef()].find(nv)].coef;

    Delta theta(( v - model.read(bv) ) / a);

    // update models of nb and bv
    model.write(bv, v);
    model.write(nv, model.read(nv)+theta);

    int nv_pos = -1; // nv's position in bv's polynomial
    // update model of Basic variables
    for (int i = 0; i < bra[lva[nv].getBindedRowsRef()].size(); i++) {
        LVRef bv_other = bra[lva[nv].getBindedRowsRef()][i].var;
        int pos = bra[lva[nv].getBindedRowsRef()][i].pos;
        if (bv_other != bv) {
            model.write(bv_other, model.read(bv_other)+pta[pa[lva[bv_other].getPolyRef()][pos]].coef * theta);
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
    for (int i = 0; i < pa[pr].size(); i++) {
        PolyTermRef ptr = pa[pr][i];
        if (pta[ptr].var == nv)
            nv_term = ptr;
        else {
            pta[ptr].coef *= inverse;
        }
    }
    polyStore.update(pr, nv_term, bv, neg_inverse);
    pta[nv_term].var = bv;
    pta[nv_term].coef = neg_inverse;

    // pr is now the new polynomial for nv
    lva[nv].setPolyRef(pr);

    printf("The result is now %s = %s\n", lva.printVar(nv), polyStore.printPoly(pr));

    // We will add bv to basic vectors so it needs to be set non-basic
    lva[bv].setNonbasic();

    // now change the attribute values for all rows where nv was present
    for (int i = 0; i < bra[lva[nv].getBindedRowsRef()].size(); i++)
    {
        // Use LRASolver::addVarToRow?
        // check that the modified row is not bv (it was changed already)
        if (bra[lva[nv].getBindedRowsRef()][i].var == bv)
            continue;
        LVRef row = bra[lva[nv].getBindedRowsRef()][i].var;
        int   pos = bra[lva[nv].getBindedRowsRef()][i].pos;
        assert( pta[pa[lva[row].getPolyRef()][pos]].coef != 0 );

        // copy a to the new Real variable (use memory pool)

        const Real& a = *newReal(&pta[pa[lva[row].getPolyRef()][pos]].coef);

        printf("The var %s = %s has an occurrence of %s at pos %d\n", lva.printVar(row), polyStore.printPoly(lva[row].getPolyRef()), lva.printVar(nv), pos);
        // Remove first nv from the poly.
        polyStore.remove(nv, lva[row].getPolyRef());
        printf("I removed %s.  My poly is now %s\n", lva.printVar(nv), polyStore.printPoly(lva[row].getPolyRef()));
        // P_i = P_i + a_nv * P_bv (iterate over all elements of P_bv)
        for (int j = 0; j < pa[pr].size(); j++) {
            LVRef col = pta[pa[pr][j]].var;
            const Real &b = pta[pa[pr][j]].coef;

            Real tmp = a*b;
            Real* p_c = newReal(&tmp);

            printf("%s + %s\n", polyStore.printPoly(lva[row].getPolyRef()), polyStore.printPolyTerm(*p_c, col));

            // Add the variable col with factor p_c to row's polynomial
            polyStore.add(row, col, *p_c);
            printf(" => %s\n", polyStore.printPoly(lva[row].getPolyRef()));
        }
    }

    // swap x and y (basicID, polynomial, bindings)
    lva[bv].setPolyRef(PolyRef_Undef);
    lva[nv].setRowId(lva[bv].getRowId());

    assert( pa[pr].has(bv) );

    Poly &p = pa[lva[nv].getPolyRef()];
    assert(bv != nv);
    bindedRowsStore.add(nv, pa[lva[nv].getPolyRef()].getPos(bv), bv);
    bra[lva[nv].getBindedRowsRef()].clear();

    assert( lva[bv].getPolyRef() == PolyRef_Undef );
    assert( pa[lva[nv].getPolyRef()].size() > 0 );
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
    if (model.read(x) < Lb(x)) {
        // add all bounds for polynomial elements, which limit lower bound
        dst.push(ba[bla[lva[x].getBounds()][lva[x].lbound()]].getPTRef());
        explanationCoefficients.push_back( Real( 1 ) );
        for (int i = 0; i < pa[lva[x].getPolyRef()].size(); i++) {
            PolyTerm &pt = pta[polyStore.getPoly(x)[i]];
            const Real &a = pt.coef;
            assert( a != 0 );
            y = columns[lva[pt.var].getColId()];
            assert(x != y);

            if (a < 0) {
                LABoundRef l_bound = bla[lva[y].getBounds()][lva[y].lbound()];
                assert(l_bound != LABoundRef_Infty);
                assert(ba[l_bound].getPTRef() != PTRef_Undef);

                dst.push(ba[l_bound].getPTRef());
                explanationCoefficients.push_back( -a );
            }
            else {
                LABoundRef u_bound = bla[lva[y].getBounds()][lva[y].ubound()];
                assert( u_bound != LABoundRef_Infty );
                assert( ba[u_bound].getPTRef() != PTRef_Undef );

                dst.push(ba[u_bound].getPTRef());
                explanationCoefficients.push_back(a);
            }
        }
    }
    if (model.read(x) > Ub(x)) {
        // add all bounds for polynomial elements, which limit upper bound
        dst.push(ba[bla[lva[y].getBounds()][lva[y].ubound()]].getPTRef());
        explanationCoefficients.push_back( Real( 1 ) );

        for (int i = 0; i < pa[lva[x].getPolyRef()].size(); i++) {
            PolyTerm &pt = pta[polyStore.getPoly(x)[i]];
            const Real &a = pt.coef;
            assert( a != 0 );
            y = columns[lva[pt.var].getColId()];
            assert(x != y);

            if (a > 0) {
                LABoundRef l_bound = bla[lva[y].getBounds()][lva[y].lbound()];
                assert(l_bound != LABoundRef_Infty);
                assert( ba[l_bound].getPTRef() != PTRef_Undef );

                dst.push( ba[l_bound].getPTRef() );
                explanationCoefficients.push_back( a );
            }
            else {
                LABoundRef u_bound = bla[lva[y].getBounds()][lva[y].ubound()];
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

void LRASolver::getSimpleDeductions(LVRef v, BoundIndex bound_idx)
{
    LABoundList& bound_list = bla[lva[v].getBounds()];
    LABoundRef br = bound_list[bound_idx];

//    printf("Deducing from bound %s\n", boundStore.printBound(br));
//    printf("The full bound list for %s:\n", logic.printTerm(lva[v].getPTRef()));
//    for (BoundIndex it = BoundIndex(0); it < BoundIndex(bound_list.size()); it=it+1)
//        printf("  %s (var %d)\n", boundStore.printBound(bound_list[it]), logic.getPterm(ba[bound_list[it]].getPTRef()).getVar());

    if (br == LABoundRef_Infty) return;
    LABound& bound = ba[br];
    if (bound.getType() == bound_l) {
        for (BoundIndex it = bound_idx - 1; it.isNonNegative(); it = it - 1) {
            LABoundRef bound_prop_ref = bound_list[it];
            LABound& bound_prop = ba[bound_prop_ref];
            if ((bound_prop.getType() == bound_l) &&
                !hasPolarity(bound_prop.getPTRef()) &&
                deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_Undef)
            {
                lbool pol = bound_prop.getSign();
                deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] = DedElem(id, pol); // id is the solver id
                th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
//                printf(" => deduced %s (var %d)\n", boundStore.printBound(bound_prop_ref), logic.getPterm(bound_prop.getPTRef()).getVar());
            }
        }
    }
    else if (bound.getType() == bound_u) {
        for (BoundIndex it = bound_idx + 1; Idx(it) < bound_list.size()-1; it = it + 1) {
            LABoundRef bound_prop_ref = bound_list[it];
            LABound& bound_prop = ba[bound_prop_ref];
            if ((bound_prop.getType() == bound_u) &&
                !hasPolarity(bound_prop.getPTRef()) &&
                (deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] == l_Undef))
            {
                lbool pol = bound_prop.getSign();
                deduced[logic.getPterm(bound_prop.getPTRef()).getVar()] = DedElem(id, pol);
                th_deductions.push(PtAsgn_reason(bound_prop.getPTRef(), pol, PTRef_Undef));
//                printf(" => deduced %s\n", boundStore.printBound(bound_prop_ref));
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
        out << bla[lva[columns[i]].getBounds()].size() << "\t";
    out << endl;

    // print the upper bounds
    for ( unsigned i = 0; i < columns.size(); i++)
        ba.printBound(bla[lva[columns[i]].getBounds()][lva[columns[i]].ubound()]);
    out << endl;

    // print the lower bounds
    for ( unsigned i = 0; i < columns.size(); i++ ) {
        ba.printBound(bla[lva[columns[i]].getBounds()][lva[columns[i]].lbound()]);
    }
    out << endl;

    // print current non-basic variables
    out << "Var:" << endl;
    for ( unsigned i = 0; i < columns.size(); i++ )
        out << logic.printTerm(lva[columns[i]].getPTRef()) << "\t";
    out << endl;

    // print current model values
    out << "Model:" << endl;
    for ( unsigned i = 0; i < columns.size(); i++)
        out << model.read(columns[i]) << "\t";
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
            if ( polyStore.getPoly(rows[i]).has(columns[j]) )
                out << pta[polyStore.getPoly(rows[i]).find(columns[j])].coef;
            out << "\t";
        }
        out << endl;
    }
}

Delta LRASolver::evalSum(PTRef tr) const {
    Pterm& t = logic.getPterm(tr);
    Delta val;
    for (int i = 0; i < t.size(); i++) {
        PTRef coef;
        PTRef var;
        logic.splitTermToVarAndConst(t[i], var, coef);
        if (removed_by_GaussianElimination.has(var) &&
            concrete_model[lva[ptermToLavar[Idx(logic.getPterm(var).getId())]].ID()] == NULL) {
            val = Delta(0); // The default
            break;
        }
        val += logic.getRealConst(coef) * model.read(ptermToLavar[Idx(logic.getPterm(var).getId())]);
    }
    return val;
}

void LRASolver::computeConcreteModel(LVRef v) {
    while (concrete_model.size() <= lva[v].ID())
        concrete_model.push(NULL);

    PTRef tr = lva[v].getPTRef();
    if (removed_by_GaussianElimination.has(tr)) {
        const vec<PTRef> &expr = *(removed_by_GaussianElimination[tr]);
        Delta val;
        for (int i = 0; i < expr.size(); i++) {
            if (logic.isRealPlus(expr[i])) { // Special case if it was the sum.
                // No guarantees here that the sum exists as an LAVar.
                int id = Idx(logic.getPterm(expr[i]).getId());
                if (id >= ptermToLavar.size() || ptermToLavar[id] == LVRef_Undef)
                    val += evalSum(expr[i]);
                else
                    val += model.read(ptermToLavar[id]);
            }
            else {
                PTRef var;
                PTRef coef;
                logic.splitTermToVarAndConst(expr[i], var, coef);
                if (removed_by_GaussianElimination.has(var) &&
                    concrete_model[lva[ptermToLavar[Idx(logic.getPterm(var).getId())]].ID()] == NULL) {
                    val = Delta(0); // The default
                    break;
                }
                val += logic.getRealConst(coef) * model.read(ptermToLavar[Idx(logic.getPterm(var).getId())]);
            }
        }
        concrete_model[lva[v].ID()] = new opensmt::Real(val.R() + val.D() * delta);
    }
    else
        concrete_model[lva[v].ID()] = new opensmt::Real(model.read(v).R() + model.read(v).D() * delta);
}


//
// Detect the appropriate value for symbolic delta and stores the model
//
void LRASolver::computeModel()
{
    assert( status == SAT );

    Real minDelta(0);
    Real maxDelta(0);
    Real curDelta(0);
    Delta curBound(Delta::ZERO);
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
        if ( boundStore.getLowerBound(col) != boundStore.minusInf()
            && ( ba[boundStore.getLowerBound(col)].getValue().D() != 0 || model.read(col).D() != 0 )
            && ( ba[boundStore.getLowerBound(col)].getValue().R() != 0 || model.read(col).R() != 0 ) )
        {
            curBound = ba[boundStore.getLowerBound(col)].getValue() - model.read(col);

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
        if ( boundStore.getUpperBound(col) != boundStore.plusInf()
            && ( ba[boundStore.getUpperBound(col)].getValue().D() != 0 || model.read(col).D() != 0 )
            && ( ba[boundStore.getUpperBound(col)].getValue().R() != 0 || model.read(col).R() != 0 ) )
        {
            curBound = model.read(col) - ba[boundStore.getUpperBound(col)].getValue();

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
    }

    // TODO: check if it is it really true :)
    assert( minDelta >= 0 );
    assert( maxDelta <= 0 );
    delta = ( minDelta ) / 2;

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

    polyStore.add(s, x, *p_v);
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

ValPair LRASolver::getValue(PTRef tr) {
    if (!logic.hasSortReal(tr)) return ValPair_Undef;
    int id = Idx(logic.getPterm(tr).getId());
    assert(id < ptermToLavar.size() && ptermToLavar[id] != LVRef_Undef);

    return ValPair(tr, concrete_model[lva[ptermToLavar[id]].ID()]->get_str().c_str());
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

