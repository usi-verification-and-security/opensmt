#include "LASolver.h"
#include "LA.h"


static SolverDescr descr_la_solver("LA Solver", "Solver for Quantifier Free Linear Arithmetics");


PtAsgn LASolver::getAsgnByBound(LABoundRef br) const {
    return LABoundRefToLeqAsgn[boundStore[br].getId()];
}

LABoundStore::BoundInfo LASolver::addBound(PTRef leq_tr) {
//    printf(" -> bound store gets %s\n", logic.pp(leq_ref));
    const Pterm& leq = logic.getPterm(leq_tr);
    PTRef const_tr = leq[0];
    PTRef sum_tr = leq[1];

    bool sum_term_is_negated = logic.isNegated(sum_tr);

    LVRef v = laVarMapper.getVarByLeqId(logic.getPterm(leq_tr).getId());
    assert(v == laVarMapper.getVarByPTId(logic.getPterm(sum_tr).getId()));

    LABoundStore::BoundInfo bi;

    LABoundRef br_pos;
    LABoundRef br_neg;

    if (sum_term_is_negated) {
        opensmt::Real constr_neg = -logic.getNumConst(const_tr);
        bi = boundStore.allocBoundPair(v, constr_neg, false);
        br_pos = bi.ub;
        br_neg = bi.lb;
    }
    else {
        const Real& constr = logic.getNumConst(const_tr);
        bi = boundStore.allocBoundPair(v, constr, true);
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
        !(LeqToLABoundRefPair[id] == LABoundRefPair{LABoundRef_Undef, LABoundRef_Undef}))
        return;

    LABoundStore::BoundInfo bi = addBound(tr);
    boundStore.updateBound(bi);
}

bool LASolver::isValid(PTRef tr)
{
    return logic.isNumLeq(tr); // MB: LA solver expects only inequalities in LEQ form!
}

void LASolver::isProperLeq(PTRef tr)
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
}

LASolver::LASolver(SolverDescr dls, SMTConfig & c, LALogic& l, vec<DedElem>& d)
        : logic(l)
        , TSolver((SolverId)descr_la_solver, (const char*)descr_la_solver, c, d)
        , laVarMapper(l, laVarStore)
        , boundStore(laVarStore)
        , model(boundStore)
        , simplex(c, model, boundStore)
{
    status = INIT;
}

void LASolver::clearSolver()
{
    status = INIT;
    simplex.clear();
    // TODO set information about columns and rows in LAVars
    TSolver::clearSolver();

    // MB: Let's keep the LAVar store and allocator
//    lva.clear();
//    lavarStore.clear();

    // also keep the bounds allocator, bounds list allocator
//    ba.clear();
//    this->bla.clear();

    this->model.clear();
    // TODO: clear statistics
//    this->tsolver_stats.clear();
    //delta = Delta::ZERO;
}

void LASolver::storeExplanation(Simplex::Explanation &&explanationBounds) {
    explanation.clear();
    for (int i = 0; i < explanationBounds.size(); i++) {
        PtAsgn asgn = getAsgnByBound(explanationBounds[i].boundref);
        explanation.push(asgn);
    }
}

bool LASolver::check_simplex(bool complete) {
    // opensmt::StopWatch check_timer(tsolver_stats.simplex_timer);
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

    getStatus() ? tsolver_stats.sat_calls ++ : tsolver_stats.unsat_calls ++;
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


bool LASolver::hasVar(PTRef expr) {
    expr =  logic.isNegated(expr) ? logic.mkNumNeg(expr) : expr;
    PTId id = logic.getPterm(expr).getId();
    return laVarMapper.hasVar(id);
}

LVRef LASolver::getLAVar_single(PTRef expr_in) {

    PTRef expr = logic.isNegated(expr_in) ? logic.mkNumNeg(expr_in) : expr_in;

    PTId id_pos = logic.getPterm(expr).getId();

    if (laVarMapper.hasVar(id_pos))
        return getVarForTerm(expr);

    LVRef x = laVarMapper.getNewVar(expr);
    return x;
}

std::unique_ptr<Polynomial> LASolver::expressionToLVarPoly(PTRef term) {

    auto poly = std::unique_ptr<Polynomial>(new Polynomial());

    bool negated = logic.isNegated(term);

    for (int i = 0; i < logic.getPterm(term).size(); i++) {
        PTRef v;
        PTRef c;
        logic.splitTermToVarAndConst(logic.getPterm(term)[i], v, c);
        LVRef var = getLAVar_single(v);
        notifyVar(var);
        Real coeff = getNum(c);
        if (negated) {
            coeff.negate();
        }
        simplex.nonbasicVar(var);
        poly->addTerm(var, std::move(coeff));
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
LVRef LASolver::exprToLVar(PTRef expr) {
    LVRef x = LVRef_Undef;
    if (laVarMapper.hasVar(expr)){
        x = getVarForTerm(expr);
        if (simplex.isProcessedByTableau(x))
        { return x;}
    }

    if (logic.isNumVar(expr) || logic.isNumTimes(expr)) {
        // Case (1), (2a), and (2b)
        PTRef v;
        PTRef c;

        logic.splitTermToVarAndConst(expr, v, c);
        assert(logic.isNumVar(v) || (logic.isNegated(v) && logic.isNumVar(logic.mkNumNeg(v))));
        x = getLAVar_single(v);
        simplex.newNonbasicVar(x);
        notifyVar(x);
    }
    else {
        // Cases (3), (4a) and (4b)
        x = getLAVar_single(expr);
        simplex.newBasicVar(x, expressionToLVarPoly(expr));
    }
    assert(x != LVRef_Undef);
    return x;
}

//
// Reads the constraint into the solver
//
void LASolver::declareAtom(PTRef leq_tr)
{
    if (!logic.isNumLeq(leq_tr)) { return; }

    if (isInformed(leq_tr)) { return; }

    setInformed(leq_tr);


    if (status != INIT)
    {
        // Treat the PTRef as it is pushed on-the-fly
        //    status = INCREMENT;
        assert( status == SAT );
    }
    // DEBUG check
    isProperLeq(leq_tr);

    const Pterm& t = logic.getPterm(leq_tr);

    while (known_preds.size() <= Idx(t.getId()))
        known_preds.push(false);
    known_preds[Idx(t.getId())] = true;
}

void LASolver::informNewSplit(PTRef tr)
{
    PTRef term = logic.getPterm(tr)[1];
    LVRef v = exprToLVar(term);
    laVarMapper.addLeqVar(tr, v);
    updateBound(tr);
}

//
// Push the constraint into the solver and increase the level
//
bool LASolver::assertLit( PtAsgn asgn, bool reason )
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

    LABoundRefPair p = getBoundRefPair(asgn.tr);
    LABoundRef bound_ref = asgn.sgn == l_False ? p.neg : p.pos;

//    printf("Model state\n");
//    model.printModelState();
//    printf("Asserting %s (%d)\n", boundStore.printBound(bound_ref), asgn.tr.x);
//    printf(" - equal to %s%s\n", asgn.sgn == l_True ? "" : "not ", logic.pp(asgn.tr));

    LVRef it = getVarForLeq(asgn.tr);
    // Constraint to push was not found in local storage. Most likely it was not read properly before
    assert(it != LVRef_Undef);
    assert(!model.isUnbounded(it));

    const Pterm& t = logic.getPterm(asgn.tr);
    // skip if it was deduced by the solver itself with the same polarity
    assert(deduced.size() > t.getVar());
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

bool LASolver::assertBoundOnVar(LVRef it, LABoundRef itBound_ref) {
    // No check whether the bounds are consistent for the polynomials.  This is done later with Simplex.

    assert(status == SAT);
    assert(it != LVRef_Undef);
    assert(!model.isUnbounded(it));
    storeExplanation(simplex.assertBoundOnVar(it, itBound_ref));

    if (explanation.size()) {
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
    model.pushBacktrackPoint();
//    printf(" -> Push backtrack point.  Following is the state of the model after the push\n");
//    model.printModelState();

    // Update the generic deductions state
    TSolver::pushBacktrackPoint();
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
        PtAsgn dec = model.popTermBacktrackPoint();
        if (dec != PtAsgn_Undef) {
            clearPolarity(dec.tr);
        }
        TSolver::popBacktrackPoint();
    }
    assert(simplex.checkValueConsistency());
//    newCandidate();
    assert(simplex.invariantHolds());
    setStatus(SAT);
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
        auto known_PTRefs = getInformed();
        for(PTRef leq_tr : known_PTRefs) {
            Pterm& leq_t = logic.getPterm(leq_tr);

            // Terms are of form c <= t where
            //  - c is a constant and
            //  - t is either a variable or a sum
            PTRef cons = leq_t[0];
            PTRef term = leq_t[1];

            // Ensure that all variables exists, build the polynomial, and update the occurrences.
            LVRef v = exprToLVar(term);

            laVarMapper.addLeqVar(leq_tr, v);

            // Assumes that the LRA variable has been already declared
            setBound(leq_tr);
        }
        boundStore.buildBounds(); // Bounds are needed for gaussian elimination
        // Gaussian Elimination should not be performed in the Incremental mode!
        if (config.lra_gaussian_elim == 1 && config.do_substitutions())
            simplifySimplex();

        model.initModel();

        status = SAT;
    }
    else
    opensmt_error( "Solver can not be initialized in the state different from INIT" );
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
        opensmt_error( "Status is undef!" );
            return false;
    }
}

//
// Sets the new solver status and returns the correspondent lbool value
//
bool LASolver::setStatus( LASolverStatus s )
{
    status = s;
    if (s == UNSAT)
        has_explanation = true;
    return getStatus( );
}


void LASolver::getSimpleDeductions(LVRef v, LABoundRef br)
{
//    printf("Deducing from bound %s\n", boundStore.printBound(br));
//    printf("The full bound list for %s:\n%s\n", logic.printTerm(lva[v].getPTRef()), boundStore.printBounds(v));

    LABound& bound = boundStore[br];
    if (bound.getValue().isInf())
        return;
    if (bound.getType() == bound_l) {
        for (int it = bound.getIdx().x - 1; it >= 0; it = it - 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound &bound_prop = boundStore[bound_prop_ref];
            if (bound_prop.getValue().isInf() || bound_prop.getType() != bound_l)
                continue;
            deduce(bound_prop_ref);
        }
    } else if (bound.getType() == bound_u) {
        for (int it = bound.getIdx().x + 1; it < boundStore.getBoundListSize(v) - 1; it = it + 1) {
            LABoundRef bound_prop_ref = boundStore.getBoundByIdx(v, it);
            LABound & bound_prop = boundStore[bound_prop_ref];
            if (bound_prop.getValue().isInf() || bound_prop.getType() != bound_u)
                continue;
            deduce(bound_prop_ref);
        }
    }
}

void LASolver::deduce(LABoundRef bound_prop) {
    PtAsgn ba = getAsgnByBound(bound_prop);
    if (!hasPolarity(ba.tr)) {
        if (deduced[logic.getPterm(ba.tr).getVar()] == l_Undef) {
            lbool pol = ba.sgn;
            deduced[logic.getPterm(ba.tr).getVar()] = DedElem(id, pol); // id is the solver id
            th_deductions.push(PtAsgn_reason(ba.tr, pol, PTRef_Undef));
        }
    }
}

//
// Prints the current state of the solver (terms, bounds, tableau)
//
void LASolver::print( ostream & out )
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


void LASolver::getConflict(bool, vec<PtAsgn>& e) {
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

// We may assume that the term is of the following forms
// (1) (* x c)
// (2) (* c x)
// (3) c
opensmt::Number LASolver::evaluateTerm(PTRef tr)
{
    Pterm& t = logic.getPterm(tr);
    opensmt::Real val(0);
    // Case (3)
    if (logic.isNumConst(tr))
        return logic.getNumConst(tr);

    // Cases (1) & (2)
    PTRef coef;
    PTRef var;
    logic.splitTermToVarAndConst(tr, var, coef);
    val += logic.getNumConst(coef) * *concrete_model[getVarId(getVarForTerm(var))];

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
ValPair LASolver::getValue(PTRef tr) {
    if (!logic.hasSortNum(tr)) return ValPair_Undef;
    PTId id = logic.getPterm(tr).getId();
    opensmt::Real val(0);
    if (!laVarMapper.hasVar(id)) {
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
        val = *concrete_model[getVarId(getVarForTerm(tr))];

    return ValPair(tr, val.get_str().c_str());
}




LASolver::~LASolver( )
{
#ifdef STATISTICS
     tsolver_stats.printStatistics(cerr);
#endif // STATISTICS
}

PtAsgn_reason LASolver::getDeduction()  { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

LALogic&  LASolver::getLogic()  { return logic; }

unsigned LASolver::nVars() const { return laVarMapper.numVars(); }



