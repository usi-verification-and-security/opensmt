/*
 *  Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2019-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#include "LASolver.h"

#include "FarkasInterpolator.h"
#include "LA.h"
#include "ModelBuilder.h"
#include "LIAInterpolator.h"
#include "CutCreator.h"
#include "Random.h"

#include <unordered_set>

static SolverDescr descr_la_solver("LA Solver", "Solver for Quantifier Free Linear Arithmetics");


PtAsgn LASolver::getAsgnByBound(LABoundRef br) const {
    return LABoundRefToLeqAsgn[boundStore[br].getId()];
}

LABoundStore::BoundInfo LASolver::addBound(PTRef leq_tr) {
    auto [const_tr, sum_tr] = logic.leqToConstantAndTerm(leq_tr);
    assert(logic.isNumConst(const_tr) && logic.isLinearTerm(sum_tr));

    bool sum_term_is_negated = laVarMapper.isNegated(sum_tr);

    LVRef v = laVarMapper.getVarByPTId(logic.getPterm(sum_tr).getId());

    LABoundStore::BoundInfo bi;
    LABoundRef br_pos;
    LABoundRef br_neg;

    if (sum_term_is_negated) {
        opensmt::Real constr_neg = -logic.getNumConst(const_tr);
        bi = boundStore.allocBoundPair(v, this->getBoundsValue(v, constr_neg, false));
        br_pos = bi.ub;
        br_neg = bi.lb;
    }
    else {
        const Real& constr = logic.getNumConst(const_tr);
        bi = boundStore.allocBoundPair(v, this->getBoundsValue(v, constr, true));
        br_pos = bi.lb;
        br_neg = bi.ub;
    }
    int br_pos_idx = boundStore[br_pos].getId();
    int br_neg_idx = boundStore[br_neg].getId();

    int tid = Idx(logic.getPterm(leq_tr).getId());
    if (LeqToLABoundRefPair.size() <= tid) {
        LeqToLABoundRefPair.growTo(tid + 1);
    }
    LeqToLABoundRefPair[tid] = LABoundRefPair{br_pos, br_neg};

    if (LABoundRefToLeqAsgn.size() <= std::max(br_pos_idx, br_neg_idx)) {
        LABoundRefToLeqAsgn.growTo(std::max(br_pos_idx, br_neg_idx) + 1);
    }
    LABoundRefToLeqAsgn[br_pos_idx] = PtAsgn(leq_tr, l_True);
    LABoundRefToLeqAsgn[br_neg_idx] = PtAsgn(leq_tr, l_False);
    return bi;
}

void LASolver::updateBound(PTRef tr)
{
    // If the bound already exists, do nothing.
    int id = Idx(logic.getPterm(tr).getId());

    if ((LeqToLABoundRefPair.size() > id) &&
        !(LeqToLABoundRefPair[id] == LABoundRefPair{LABoundRef_Undef, LABoundRef_Undef})) {
        return;
    }

    LABoundStore::BoundInfo bi = addBound(tr);
    boundStore.updateBound(bi);
}

bool LASolver::isValid(PTRef tr)
{
    return logic.isLeq(tr); // MB: LA solver expects only inequalities in LEQ form!
}

void LASolver::isProperLeq(PTRef tr)
{
    assert(logic.isAtom(tr));
    assert(logic.isLeq(tr));
    auto [cons, sum] = logic.leqToConstantAndTerm(tr);
    assert(logic.isConstant(cons));
    assert(logic.isNumVar(sum) || logic.isPlus(sum) || logic.isTimes(sum));
    assert(!logic.isTimes(sum) || ((logic.isNumVar(logic.getPterm(sum)[0]) && logic.isOne(logic.mkNeg(logic.getPterm(sum)[1]))) ||
                                   (logic.isNumVar(logic.getPterm(sum)[1]) && logic.isOne(logic.mkNeg(logic.getPterm(sum)[0])))));
    (void) cons; (void)sum;
}

LASolver::LASolver(SMTConfig & c, ArithLogic & l) : LASolver(descr_la_solver, c, l) {}

LASolver::LASolver(SolverDescr dls, SMTConfig & c, ArithLogic & l)
        : TSolver((SolverId) dls, (const char *) dls, c)
        , logic(l)
        , laVarMapper(l)
        , boundStore(laVarStore)
        , simplex(boundStore)
{
    dec_limit.push(0);
    status = INIT;
}


int LASolver::backtrackLevel() {
    return dec_limit.size() - 1;
}

void LASolver::pushDecision(PtAsgn asgn)
{
    int_decisions.push({asgn, backtrackLevel()});
    decision_trace.push(asgn);
}

void LASolver::clearSolver()
{
    status = INIT;
    simplex.clear();
    decision_trace.clear();
    int_decisions.clear();
    dec_limit.clear();
    TSolver::clearSolver();

    laVarStore.clear();
    laVarMapper.clear();
    boundStore.clear();
    LABoundRefToLeqAsgn.clear();
    LeqToLABoundRefPair.clear();

    int_vars.clear();
    int_vars_map.clear();
    // TODO: clear statistics
//    this->egraphStats.clear();
}

void LASolver::storeExplanation(Simplex::Explanation &&explanationBounds) {
    explanation.clear();
    explanationCoefficients.clear();
    for (std::size_t i = 0; i < explanationBounds.size(); i++) {
        PtAsgn asgn = getAsgnByBound(explanationBounds[i].boundref);
        explanation.push(asgn);
        explanationCoefficients.push_back(explanationBounds[i].coeff);
    }
}

bool LASolver::check_simplex(bool complete) {
    // opensmt::StopWatch check_timer(egraphStats.simplex_timer);
//    printf(" - check %d\n", debug_check_count++);
    (void)complete;
    // check if we stop reading constraints
    if (status == INIT) {
        initSolver();
    }
    storeExplanation(simplex.checkSimplex());

    if (explanation.size() == 0)
        setStatus(SAT);
    else {
        setStatus(UNSAT);
    }

    getStatus() ? generalTSolverStats.sat_calls ++ : generalTSolverStats.unsat_calls ++;
//    printf(" - check ended\n");
//    printf(" => %s\n", getStatus() ? "sat" : "unsat");
//    if (getStatus())
//        model.printModelState();
    return getStatus();
}

//
// The model system
//
/*
bool LASolver::isModelOutOfBounds(LVRef v) const {
    return simplex.isModelOutOfBounds(v);
}

bool LASolver::isModelOutOfUpperBound(LVRef v) const
{
    return simplex.isModelOutOfBounds(v);
}

bool LASolver::isModelOutOfLowerBound(LVRef v) const
{
    return ( model.read(v) < model.Lb(v) );
}


const Delta LASolver::overBound(LVRef v) const
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
*/

void LASolver::setBound(PTRef leq_tr)
{
//    printf("Setting bound for %s\n", logic.printTerm(leq_tr));

    addBound(leq_tr);
}

opensmt::Number LASolver::getNum(PTRef r) {
    return logic.getNumConst(r);
}

void LASolver::notifyVar(LVRef v) {
    assert(logic.isNumVar(getVarPTRef(v)));
    if (logic.yieldsSortInt(getVarPTRef(v))) {
        markVarAsInt(v);
    }
}

void LASolver::markVarAsInt(LVRef v) {
    if (!int_vars_map.has(v)) {
        int_vars_map.insert(v, true);
        int_vars.push(v);
    }
}

LVRef LASolver::getVarForLeq(PTRef ref) const {
    assert(logic.isLeq(ref));
    auto [constant, term] = logic.leqToConstantAndTerm(ref);
    return laVarMapper.getVarByPTId(logic.getPterm(term).getId());
}

LVRef LASolver::getLAVar_single(PTRef expr_in) {

    assert(logic.isLinearTerm(expr_in));
    PTId id = logic.getPterm(expr_in).getId();

    if (laVarMapper.hasVar(id)) {
        return getVarForTerm(expr_in);
    }

    PTRef expr = laVarMapper.isNegated(expr_in) ? logic.mkNeg(expr_in) : expr_in;
    LVRef x = laVarStore.getNewVar();
    laVarMapper.registerNewMapping(x, expr);
    return x;
}

std::unique_ptr<Tableau::Polynomial> LASolver::expressionToLVarPoly(PTRef term) {
    auto poly = std::make_unique<Tableau::Polynomial>();
    bool negated = laVarMapper.isNegated(term);
    for (int i = 0; i < logic.getPterm(term).size(); i++) {
        auto [v,c] = logic.splitTermToVarAndConst(logic.getPterm(term)[i]);
        LVRef var = getLAVar_single(v);
        Real coeff = getNum(c);
        if (negated) {
            coeff.negate();
        }
        poly->addTerm(var, std::move(coeff));
    }
    return poly;
}


//
// Registers an arithmetic Pterm (polynomial) with the solver.
// We may assume that the term is of one of the following forms,
// where x is a variable or ite, and p_i are products of a variable or ite and a constant
//
// (1) x
// (2a) (* x -1)
// (2b) (* -1 x)
// (3) x + p_1 + ... + p_n
// (4a) (* x -1) + p_1 + ... + p_n
// (4b) (* -1 x) + p_1 + ... + p_n
//
// Returns internalized reference for the term
LVRef LASolver::registerArithmeticTerm(PTRef expr) {
    LVRef x = LVRef::Undef;
    if (laVarMapper.hasVar(expr)){
        x = getVarForTerm(expr);
        if (simplex.isProcessedByTableau(x)){
            return x;
        }
    }

    if (logic.isNumVar(expr) || logic.isTimes(expr)) {
        // Case (1), (2a), and (2b)
        auto [v,c] = logic.splitTermToVarAndConst(expr);
        assert(logic.isNumVar(v) || (laVarMapper.isNegated(v) && logic.isNumVar(logic.mkNeg(v))));
        x = getLAVar_single(v);
        simplex.newNonbasicVar(x);
        notifyVar(x);
    }
    else {
        // Cases (3), (4a) and (4b)
        x = getLAVar_single(expr);
        auto poly = expressionToLVarPoly(expr);
        // ensure the simplex knows about all the variables
        // and compute if this poly is always integer
        bool isInt = true;
        for (auto const & term : *poly) {
            notifyVar(term.var);
            simplex.nonbasicVar(term.var);
            // MB: Notify must be called before the query isIntVar!
            isInt &= isIntVar(term.var) && term.coeff.isInteger();
        }
        simplex.newRow(x, std::move(poly));
        if (isInt) {
            markVarAsInt(x);
        }
    }
    assert(x != LVRef::Undef);
    return x;
}

//
// Reads the constraint into the solver
//
void LASolver::declareAtom(PTRef leq_tr)
{
    if (!logic.isLeq(leq_tr)) { return; }

    if (isInformed(leq_tr)) { return; }

    setInformed(leq_tr);

    if (status != INIT)
    {
        // Treat the PTRef as it is pushed on-the-fly
        //    status = INCREMENT;
        assert( status == SAT );
        PTRef term = logic.getPterm(leq_tr)[1];
        registerArithmeticTerm(term);
        updateBound(leq_tr);
    }
    // DEBUG check
    isProperLeq(leq_tr);
}

LVRef LASolver::splitOnRandom(vec<LVRef> const & varsToFix) {
    int pick = opensmt::irand(seed, varsToFix.size());
    return varsToFix[pick];
}

TRes LASolver::checkIntegersAndSplit() {

    vec<LVRef> varsToFix;
    varsToFix.capacity(int_vars.size());

    for (LVRef x : int_vars) {
        if (not isModelInteger(x)) {
            assert(not simplex.hasLBound(x) or not simplex.hasUBound(x) or simplex.Ub(x) - simplex.Lb(x) >= 1);
            varsToFix.push(x);
        }
    }

    if (varsToFix.size() == 0) {
        setStatus(SAT);
        return TRes::SAT;
    }

    if (shouldTryCutFromProof()) {
        auto res = cutFromProof();
        if (res != TRes::UNKNOWN) {
            return res;
        }
    }

    LVRef chosen = splitOnRandom(varsToFix);

    assert(chosen != LVRef::Undef);
    auto splitLowerVal = simplex.getValuation(chosen).R().floor();
    //x <= c || x >= c+1;
    PTRef varPTRef = getVarPTRef(chosen);
    PTRef upperBound = logic.mkLeq(varPTRef, logic.mkIntConst(splitLowerVal));
    PTRef lowerBound = logic.mkGeq(varPTRef, logic.mkIntConst(splitLowerVal + 1));
    PTRef constr = logic.mkOr(upperBound, lowerBound);

    splitondemand.push(constr);
    setStatus(NEWSPLIT);
    return TRes::SAT;
}

void LASolver::getNewSplits(vec<PTRef>& splits) {
    splitondemand.copyTo(splits);
    splitondemand.clear();
    setStatus(SAT);
}


//
// Push the constraint into the solver and increase the level
//
bool LASolver::assertLit(PtAsgn asgn)
{
    assert(asgn.sgn != l_Undef);

//    printf("Assert %d\n", debug_assert_count++);

    // Special cases of the "inequalitites"
    if (logic.isTrue(asgn.tr) && asgn.sgn == l_True) {
        generalTSolverStats.sat_calls ++;
        return true;
    }
    if (logic.isFalse(asgn.tr) && asgn.sgn == l_False) {
        generalTSolverStats.sat_calls ++;
        return true;
    }
    if (logic.isTrue(asgn.tr) && asgn.sgn == l_False) {
        generalTSolverStats.unsat_calls ++;
        return false;
    }
    if (logic.isFalse(asgn.tr) && asgn.sgn == l_True) {
        generalTSolverStats.unsat_calls ++;
        return false;
    }
    // check if we stop reading constraints
    if( status == INIT  )
        initSolver( );


    if (hasPolarity(asgn.tr) && getPolarity(asgn.tr) == asgn.sgn) {
        // already known, no new information
        // MB: The deductions done by this TSolver are also marked using polarity.
        //     The invariant is that TSolver will not process the literal again (when asserted from the SAT solver)
        //     once it is marked for deduction, so the implementation must count with that.
        assert(getStatus());
        generalTSolverStats.sat_calls ++;
        return getStatus();
    }

    LABoundRefPair p = getBoundRefPair(asgn.tr);
    LABoundRef bound_ref = asgn.sgn == l_False ? p.neg : p.pos;

//    printf("Model state\n");
//    model.printModelState();
//    printf("Asserting %s (%d)\n", boundStore.printBound(bound_ref), asgn.tr.x);
//    printf(" - equal to %s%s\n", asgn.sgn == l_True ? "" : "not ", logic.pp(asgn.tr));

    if (assertBound(bound_ref)) {
        assert(getStatus());
        setPolarity(asgn.tr, asgn.sgn);
        pushDecision(asgn);
        getSimpleDeductions(bound_ref);
        generalTSolverStats.sat_calls++;
    } else {
        generalTSolverStats.unsat_calls++;
    }

    return getStatus();
}

bool LASolver::assertBound(LABoundRef boundRef) {
    // No check whether the bounds are consistent for the polynomials.  This is done later with Simplex.
    assert(status == SAT);
    storeExplanation(simplex.assertBound(boundRef));

    if (explanation.size() > 0) {
        return setStatus(UNSAT);
    }
    return getStatus();
}



//
// Push the solver one level down
//
void LASolver::pushBacktrackPoint( )
{
    // Check if any updates need to be repeated after backtrack
    simplex.pushBacktrackPoint();
    dec_limit.push(decision_trace.size());

    // Update the generic deductions state
    TSolver::pushBacktrackPoint();
}

PtAsgn
LASolver::popDecisions()
{
    PtAsgn popd = PtAsgn_Undef;
    assert(decision_trace.size() - dec_limit.last() == 1 || decision_trace.size() - dec_limit.last() == 0);
    if (decision_trace.size() - dec_limit.last() == 1) {
        popd = int_decisions.last().asgn;
        int_decisions.pop();
    }
    decision_trace.shrink(decision_trace.size() - dec_limit.last());
    return popd;
}

PtAsgn LASolver::popTermBacktrackPoint() {
    simplex.popBacktrackPoint();
    PtAsgn popd = popDecisions();
    dec_limit.pop();
    return popd;
}

// Pop the solver one level up
// NOTE: this method should not be used, pop multiple points is more efficient with popBacktrackPoints rather than popping one by one
void LASolver::popBacktrackPoint( ) {
    this->popBacktrackPoints(1);
}

// Pop the solver given number of times
//
void LASolver::popBacktrackPoints(unsigned int count) {
    for ( ; count > 0; --count){
        PtAsgn dec = popTermBacktrackPoint();
        if (dec != PtAsgn_Undef) {
            clearPolarity(dec.tr);
            LVRef it = getVarForLeq(dec.tr);
            simplex.boundDeactivated(it);
        }

        TSolver::popBacktrackPoint();
    }
    simplex.finalizeBacktracking();
    if(status != INIT){
        setStatus(SAT);
    }
}

void LASolver::initSolver()
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
        const auto & known_PTRefs = getInformed();
        for(PTRef leq_tr : known_PTRefs) {
            Pterm const & leq_t = logic.getPterm(leq_tr);

            // Terms are of form c <= t where
            //  - c is a constant and
            //  - t is either a variable or a sum
            // leq_t[0] is const and leq_t[1] is term
            PTRef term = leq_t[1];

            // Ensure that all variables exists, build the polynomial, and update the occurrences.
            registerArithmeticTerm(term);

            // Assumes that the LRA variable has been already declared
            setBound(leq_tr);
        }
        boundStore.buildBounds(); // Bounds are needed for gaussian elimination

        simplex.initModel();

        status = SAT;
    }
    else {
        throw OsmtInternalException("Solver can not be initialized in the state different from INIT");
    }
}

//
// Returns boolean value correspondent to the current solver status
//
inline bool LASolver::getStatus( )
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
        case NEWSPLIT:
        {
            return true;
            break;
        }
        case UNKNOWN:
//            cerr << "LA Solver status is unknown" << endl;
            status = SAT;
            return true;
        case INIT:
        case ERROR:
        default:
            throw OsmtApiException("Status is undef!");
    }
}

//
// Sets the new solver status and returns the correspondent lbool value
//
bool LASolver::setStatus( LASolverStatus s )
{
    status = s;
    has_explanation = (s == UNSAT);
    return getStatus( );
}


void LASolver::getSimpleDeductions(LABoundRef br)
{
//    printf("Deducing from bound %s\n", boundStore.printBound(br));
//    printf("The full bound list for %s:\n%s\n", logic.printTerm(lva[v].getPTRef()), boundStore.printBounds(v));

    auto const & bound = boundStore[br];
    LVRef v = bound.getLVRef();
    if (bound.getType() == bound_l) {
        for (int it = bound.getIdx().x - 1; it >= 0; it = it - 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound &bound_prop = boundStore[bound_prop_ref];
            if (bound_prop.getType() != bound_l)
                continue;
            deduce(bound_prop_ref);
        }
    } else if (bound.getType() == bound_u) {
        for (int it = bound.getIdx().x + 1; it < boundStore.getBounds(v).size() - 1; it = it + 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound & bound_prop = boundStore[bound_prop_ref];
            if (bound_prop.getType() != bound_u)
                continue;
            deduce(bound_prop_ref);
        }
    }
}

void LASolver::deduce(LABoundRef bound_prop) {
    PtAsgn ba = getAsgnByBound(bound_prop);
    if (!hasPolarity(ba.tr)) {
        storeDeduction(PtAsgn_reason(ba.tr, ba.sgn, PTRef_Undef));
    }
}


void LASolver::getConflict(vec<PtAsgn> & conflict) {
    for (PtAsgn lit : explanation) {
        conflict.push(lit);
    }
}

void LASolver::fillTheoryFunctions(ModelBuilder & modelBuilder) const {
    for (LVRef lvar : laVarStore) {
        PTRef term = laVarMapper.getVarPTRef(lvar);
        if (logic.isNumVar(term)) {
            PTRef val = logic.mkConst(logic.getSortRef(term), concrete_model[getVarId(lvar)]);
            modelBuilder.addVarValue(term, val);
        }
    }
}


void LASolver::computeConcreteModel(LVRef v, const opensmt::Real& delta) {
    while (concrete_model.size() <= getVarId(v))
        concrete_model.push_back(0);
    Delta val = simplex.getValuation(v);
    concrete_model[getVarId(v)] = val.R() + val.D() * delta;
}


//
// Detect the appropriate value for symbolic delta and stores the model
//

void LASolver::computeModel()
{
    assert( status == SAT );
    opensmt::Real delta = simplex.computeDelta();

    for (LVRef var : laVarStore)
    {
        computeConcreteModel(var, delta);
    }
}


LASolver::~LASolver( )
{
#ifdef STATISTICS
    printStatistics(std::cerr);
#endif // STATISTICS
}

ArithLogic&  LASolver::getLogic()  { return logic; }


/**
 * Given an inequality v ~ c (with ~ is either < or <=), compute the correct bounds on the variable.
 * The correct values of the bounds are computed differently, based on whether the value of v must be Int or not.
 *
 * @param c Real number representing the upper bound
 * @param strict inequality is LEQ if false, LT if true
 * @return The values of upper and lower bound corresponding to the inequality
 */
LABoundStore::BoundValuePair LASolver::getBoundsValue(LVRef v, const Real & c, bool strict) {
    return isIntVar(v) ? getBoundsValueForIntVar(c, strict) : getBoundsValueForRealVar(c, strict);
}

/**
 * Given an imaginary inequality v ~ c (with ~ is either < or <=), compute the interger bounds on the variable
 *
 * @param c Real number representing the upper bound
 * @param strict inequality is LEQ if false, LT if true
 * @return The integer values of upper and lower bound corresponding to the inequality
 */
LABoundStore::BoundValuePair LASolver::getBoundsValueForIntVar(const Real & c, bool strict) {
    if (strict) {
        // v < c => UB is ceiling(c-1), LB is ceiling(c)
        return {Delta((c-1).ceil()), Delta(c.ceil())};
    }
    else {
        // v <= c => UB is floor(c), LB is floor(c+1)
        return {Delta(c.floor()), Delta((c+1).floor())};
    }
}


/**
 * Given an imaginary inequality v ~ c (with ~ is either < or <=), compute the real bounds on the variable
 *
 * @param c Real number representing the upper bound
 * @param strict inequality is LEQ if false, LT if true
 * @return The real values of upper and lower bound corresponding to the inequality
 */
LABoundStore::BoundValuePair LASolver::getBoundsValueForRealVar(const Real & c, bool strict) {
    if (strict) {
        // v < c => UB is c-\delta, LB is c
        return { Delta(c, -1), Delta(c) };
    }
    else {
        // v <= c => UB is c, LB is c+\delta
        return { Delta(c), Delta(c, 1) };
    }
}

lbool LASolver::getPolaritySuggestion(PTRef ptref) const {
    if (!this->isInformed(ptref)) { return l_Undef; }
    LVRef var = this->getVarForLeq(ptref);
    LABoundRefPair bounds = getBoundRefPair(ptref);
    assert( bounds.pos != LABoundRef_Undef && bounds.neg != LABoundRef_Undef );
    return simplex.getPolaritySuggestion(var, bounds.pos, bounds.neg);
}

TRes LASolver::check(bool complete) {
    bool rval = check_simplex(complete);
    if (complete && rval) {
        return checkIntegersAndSplit();
    }
    return rval ? TRes::SAT : TRes::UNSAT;
}

bool LASolver::isModelInteger(LVRef v) const
{
    Delta val = simplex.getValuation(v);
    return !( val.hasDelta() || !val.R().isInteger() );
}

PTRef LASolver::interpolateUsingEngine(FarkasInterpolator & interpolator) const {
    auto itpAlgorithm = config.getLRAInterpolationAlgorithm();
    if (itpAlgorithm == itp_lra_alg_strong) { return interpolator.getFarkasInterpolant(); }
    else if (itpAlgorithm == itp_lra_alg_weak) { return interpolator.getDualFarkasInterpolant(); }
    else if (itpAlgorithm == itp_lra_alg_factor) { return interpolator.getFlexibleInterpolant(opensmt::Real(config.getLRAStrengthFactor())); }
    else if (itpAlgorithm == itp_lra_alg_decomposing_strong) { return interpolator.getDecomposedInterpolant(); }
    else if (itpAlgorithm == itp_lra_alg_decomposing_weak) { return interpolator.getDualDecomposedInterpolant(); }
    else {
        assert(false); // Incorrect value in config
        return interpolator.getFarkasInterpolant();
    }
}

//
// Compute interpolants for the conflict
//
PTRef
LASolver::getRealInterpolant( const ipartitions_t & mask , ItpColorMap * labels, PartitionManager &pmanager) {
    assert(status == UNSAT);
    vec<PtAsgn> explCopy;
    explanation.copyTo(explCopy);
    FarkasInterpolator interpolator(logic, std::move(explCopy), explanationCoefficients, labels ? *labels : ItpColorMap{},
        std::make_unique<GlobalTermColorInfo>(pmanager, mask));
    return interpolateUsingEngine(interpolator);
}

PTRef LASolver::getIntegerInterpolant(ItpColorMap const& labels) {
    assert(status == UNSAT);
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, explanation, explanationCoefficients, labels));
    return interpolateUsingEngine(interpolator);
}

void LASolver::printStatistics(std::ostream & out) {
    TSolver::printStatistics(out);
    laSolverStats.printStatistics(out);
}

bool LASolver::shouldTryCutFromProof() const {
    if (this->config.produce_inter()) { return false; }
    static unsigned long counter = 0;
    return ++counter % 10 == 0;
}

namespace {

struct DefiningConstraint {
    PTRef lhs;
    opensmt::Real rhs;
};

/*
 * Translates the set of defining constraints (linear equalities) into a suitable inner representation:
 * - A sparse matrix A of coefficients and constants b
 * - a map from column indices to the corresponding variables x
 * - The result is to be interpreted as the linear system Ax = b
 */
std::pair<SparseLinearSystem,std::vector<PTRef>> linearSystemFromConstraints(std::vector<DefiningConstraint> const & constraints, ArithLogic & logic) {
    vec<PTRef> terms;
    auto fillTerms = [&logic](PTRef poly, vec<PTRef> & terms) {// reduces linear polynomial to a vector of the polynomial's terms
        terms.clear();
        if (logic.isPlus(poly)) {
            for (PTRef arg : logic.getPterm(poly)) {
                terms.push(arg);
            }
        } else {
            terms.push(poly);
        }
    };
    std::unordered_map<PTRef, unsigned, PTRefHash> varIndices;
    uint32_t columns = 0;
    // First pass to assign indices and find out number of columns
    for (auto const & defConstraint : constraints) {
        PTRef poly = defConstraint.lhs;
        fillTerms(poly, terms);
        for (PTRef arg : terms) {
            auto [var, constant] = logic.splitTermToVarAndConst(arg);
            assert(var != PTRef_Undef);
            if (varIndices.find(var) == varIndices.end()) {
                varIndices.insert({var, columns++});
            }
        }
    }

    uint32_t rows = constraints.size();
    SparseColMatrix matrixA(RowCount{rows}, ColumnCount{columns});
    std::vector<FastRational> rhs(rows);
    std::vector<SparseColMatrix::ColumnPolynomial> columnPolynomials(columns);

    // Second pass to build the actual matrix
    for (unsigned row = 0; row < constraints.size(); ++row) {
        rhs[row] = constraints[row].rhs;
        PTRef poly = constraints[row].lhs;
        fillTerms(poly, terms);
        for (PTRef arg : terms) {
            auto [var, constant] = logic.splitTermToVarAndConst(arg);
            auto col = varIndices[var];
            columnPolynomials[col].addTerm(IndexType{row}, logic.getNumConst(constant));
        }
    }
    for (uint32_t i = 0; i < columnPolynomials.size(); ++i) {
        matrixA.setColumn(ColIndex{i}, std::move(columnPolynomials[i]));
    }
    // compute the inverse map from column indices to variables
    std::vector<PTRef> columnMapping(matrixA.colCount(), PTRef_Undef);
    for (auto [var, index] : varIndices) {
        columnMapping[index] = var;
    }

    assert(matrixA.colCount() == columnMapping.size());

    return {SparseLinearSystem{std::move(matrixA), std::move(rhs)}, std::move(columnMapping)};
}

PTRef getSumFromTermVec(SparseColMatrix::TermVec const & termVec, vec<PTRef> const & toVarMap, ArithLogic & logic) {
    vec<PTRef> args;
    for (auto const & term : termVec) {
        IndexType var = term.first;
        auto const & coeff = term.second;
        args.push(logic.mkTimes(toVarMap[var.x], logic.mkIntConst(coeff)));
    }
    return logic.mkPlus(std::move(args));
}

PTRef cutToSplit(CutCreator::Cut && cut, std::vector<PTRef> const & toVarMap, ArithLogic & logic) {
    auto const & termVec = cut.first;
    auto const & rhs = cut.second;
    if (termVec.empty()) {
        return PTRef_Undef;
    }
    PTRef constraint = getSumFromTermVec(termVec, toVarMap, logic);
    auto lowerBoundValue = rhs.ceil();
    auto upperBoundValue = rhs.floor();
    PTRef upperBound = logic.mkLeq(constraint, logic.mkIntConst(upperBoundValue));
    PTRef lowerBound = logic.mkGeq(constraint, logic.mkIntConst(lowerBoundValue));
    return logic.mkOr(upperBound, lowerBound);
}
}

TRes LASolver::cutFromProof() {
    auto isOnLowerBound = [this](LVRef var) { return simplex.hasLBound(var) and not simplex.isModelStrictlyOverLowerBound(var); };
    auto isOnUpperBound = [this](LVRef var) { return simplex.hasUBound(var) and not simplex.isModelStrictlyUnderUpperBound(var); };
    // Step 1: Gather defining constraints
    std::vector<DefiningConstraint> constraints;
    for (LVRef var : int_vars) {
        bool isOnLower = isOnLowerBound(var);
        bool isOnUpper = isOnUpperBound(var);
        if (not isOnLower and not isOnUpper) { continue; }

        PTRef term = laVarMapper.getVarPTRef(var);
        auto const & val = isOnLower ? simplex.Lb(var) : simplex.Ub(var);
        assert(not val.hasDelta());
        auto const & rhs = val.R();
        assert(rhs.isInteger());
        if (isOnLower and isOnUpper) {
            constraints.insert(constraints.begin(), DefiningConstraint{term, rhs});
        } else {
            constraints.push_back(DefiningConstraint{term, rhs});
        }

//        std::cout << logic.pp(term) << " = " << rhs << std::endl;
    }
    auto getVarValue = [this](PTRef var) {
        assert(this->logic.isVar(var));
        LVRef lvar = this->laVarMapper.getVarByPTId(logic.getPterm(var).getId());
        Delta val = this->simplex.getValuation(lvar);
        assert(not val.hasDelta());
        return val.R();
    };
    CutCreator cutCreator(getVarValue);
    auto [system, toVarMap] = linearSystemFromConstraints(constraints, logic);
    auto cut = cutCreator.makeCut(std::move(system), toVarMap);
    PTRef split = cutToSplit(std::move(cut), toVarMap, logic);
    if (split == PTRef_Undef) {
        return TRes::UNKNOWN;
    }
    splitondemand.push(split);
    setStatus(NEWSPLIT);
    return TRes::SAT;
}

vec<PTRef> LASolver::collectEqualitiesFor(vec<PTRef> const & vars, std::unordered_set<PTRef, PTRefHash> const & knownEqualities) {
    struct DeltaHash {
        std::size_t operator()(Delta const & d) const {
            FastRationalHash hasher;
            return (hasher(d.R()) ^ hasher(d.D()));
        }
    };

    vec<PTRef> equalities;
    std::unordered_map<Delta, vec<PTRef>, DeltaHash> eqClasses;
    for (PTRef var : vars) {
        if (logic.isNumConst(var)) {
            eqClasses[logic.getNumConst(var)].push(var);
        } else {
            assert(logic.isNumVar(var));
            if (not laVarMapper.hasVar(var)) { // LASolver does not have any constraints on this LA var
                continue;
            }
            LVRef v = laVarMapper.getVarByPTId(logic.getPterm(var).getId());
            auto value = simplex.getValuation(v);
            eqClasses[value].push(var);
        }
    }

    for (auto const & entry : eqClasses) {
        auto const & equivalentVars = entry.second;
        for (int i = 0; i < equivalentVars.size(); ++i) {
            for (int j = i + 1; j < equivalentVars.size(); ++j) {
                PTRef eq = logic.mkEq(equivalentVars[i], equivalentVars[j]);
                if (knownEqualities.find(eq) == knownEqualities.end()) {
                    equalities.push(eq);
                }
            }
        }
    }

    // Hack to ensure that when model is computed, delta is not picked so that it merges some of the equivalence
    // classes that are different at this point
    if (equalities.size() == 0 and not eqClasses.empty()) {
        std::vector<Delta> valuesWithDelta;
        for (auto const & entry : eqClasses) {
            if (entry.first.hasDelta()) {
                valuesWithDelta.push_back(entry.first);
            }
        }
        for (auto const & val : valuesWithDelta) {
            for (auto const & entry : eqClasses) {
                // check if entry.first - val could be 0 for some value of delta, with 0 < delta <= maxDelta
                auto diff = entry.first - val;
                if (not diff.hasDelta()) { continue; } // MB: This takes care also of the case where val == entry.first
                if (isNonNegative(diff.R()) and isPositive(diff.D())) { continue; }
                if (isNonPositive(diff.R()) and isNegative(diff.D())) { continue; }
                auto ratio = diff.R() / diff.D();
                assert(isNegative(ratio));
                ratio.negate(); // MB: delta is the negated ratio
                if (ratio > Simplex::maxDelta) { continue; } // No chance of collision

                // They could be equal for the right value of delta, add equalities for cross-product
                vec<PTRef> const & varsOfFirstVal = eqClasses.at(val);
                vec<PTRef> const & varsOfSecondVal = entry.second;

                for (PTRef var1 : varsOfFirstVal) {
                    for (PTRef var2 : varsOfSecondVal) {
                        PTRef eq = logic.mkEq(var1, var2);
                        if (knownEqualities.find(eq) == knownEqualities.end()) {
                            equalities.push(eq);
                            // MB: It should be OK to decide one such equality, we do not have to add whole cross-product at once
                            return equalities;
                        }
                    }
                }
            }
        }
    }
    return equalities;
}
