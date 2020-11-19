//
// Created by prova on 06.09.19.
//

#include "Simplex.h"

#include <limits>
#include <algorithm>

#ifdef SIMPLEX_DEBUG
#define simplex_assert(x) assert(x)
#else
#define simplex_assert(x)
#endif // SIMPLEX_DEBUG

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

Simplex::Explanation Simplex::checkSimplex() {
    processBufferOfActivatedBounds();
    bool bland_rule = false;
    unsigned repeats = 0;

    // keep doing pivotAndUpdate until the SAT/UNSAT status is confirmed
    while (true) {
        repeats++;
        LVRef x = LVRef_Undef;

        if (!bland_rule && (repeats > tableau.getNumOfCols()))
            bland_rule = true;

        if (bland_rule) {
            x = getBasicVarToFixByBland();
            ++simplex_stats.num_bland_ops;
        }
        else {
            x = getBasicVarToFixByShortestPoly();
            ++simplex_stats.num_pivot_ops;
        }

        if (x == LVRef_Undef) {
            // SAT
            refineBounds();
            model->saveAssignment();
            return Explanation();
        }

        LVRef y_found = LVRef_Undef;
        if (bland_rule){
            y_found = findNonBasicForPivotByBland(x);
        }
        else{
            y_found = findNonBasicForPivotByHeuristic(x);
        }
        // if it was not found - UNSAT
        if (y_found == LVRef_Undef) {
            assert(isModelOutOfBounds(x));
            bool isOutOfLowerBound = isModelOutOfLowerBound(x);
            model->restoreAssignment();
            return getConflictingBounds(x, isOutOfLowerBound);
        }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
        else {
            pivot(x, y_found);
        }
    }
}

const Delta Simplex::overBound(LVRef v) const {
    assert(isModelOutOfBounds(v));
    if (isModelOutOfUpperBound(v)) {
        return (Delta(model->read(v) - model->Ub(v)));
    } else if (isModelOutOfLowerBound(v)) {
        return (Delta(model->Lb(v) - model->read(v)));
    }
    assert (false);
    printf("Problem in overBound, LRASolver.C:%d\n", __LINE__);
    exit(1);
}

bool Simplex::isUnbounded(LVRef v) const {
    return model->isUnbounded(v);
}

LVRef Simplex::getBasicVarToFixByShortestPoly() const {
    assert(std::all_of(candidates.begin(), candidates.end(),
                       [&](LVRef var) {
                           return var != LVRef_Undef && tableau.isBasic(var) && isModelOutOfBounds(var);
                       }));
    // MB: replace this with std::min_element when ranges are available (to avoid duplicate calls to getPolySize)
    LVRef current = LVRef_Undef;
    std::size_t current_poly_size = std::numeric_limits<std::size_t>::max();
    for (auto it : candidates) { // Select the var with smallest row
        bool const doUpdate = tableau.getPolySize(it) < current_poly_size;
        if (doUpdate) {
            current = it;
            current_poly_size = tableau.getPolySize(it);
        }
    }
    return current;
}

LVRef Simplex::getBasicVarToFixByBland() const {
    assert(std::all_of(candidates.begin(), candidates.end(),
                       [&](LVRef var) {
                           return var != LVRef_Undef && tableau.isBasic(var) && isModelOutOfBounds(var);
                       }));
    // MB: replace this with std::min_element when ranges are available (to avoid duplicate calls to getVarId)
    auto curr_var_id_x = std::numeric_limits<unsigned>::max();
    LVRef current = LVRef_Undef;
    for (auto it : candidates) { // Select the var with the smallest id
        auto const id = getVarId(it);
        bool const doUpdate = id < curr_var_id_x;
        if (doUpdate) {
            current = it;
            curr_var_id_x = id;
        }
    }
    return current;
}

LVRef Simplex::findNonBasicForPivotByHeuristic(LVRef basicVar) {
    // favor more independent variables: those present in less rows
    assert(tableau.isBasic(basicVar));
    LVRef v_found = LVRef_Undef;
    if (isModelOutOfLowerBound(basicVar)) {

        for (auto const &term : tableau.getRowPoly(basicVar)) {
            auto var = term.var;
            assert(tableau.isNonBasic(var));
            assert(var != basicVar);
            auto const &coeff = term.coeff;
            const bool is_coeff_pos = coeff > 0;

            if ((is_coeff_pos && isModelStrictlyUnderUpperBound(var)) ||
                (!is_coeff_pos && isModelStrictlyOverLowerBound(var))) {
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
    else if (isModelOutOfUpperBound(basicVar)) {

        for (auto const &term : tableau.getRowPoly(basicVar)) {
            auto var = term.var;
            assert(tableau.isNonBasic(var));
            assert(var != basicVar);
            auto const &coeff = term.coeff;
            const bool is_coeff_pos = coeff > 0;

            if ((!is_coeff_pos && isModelStrictlyUnderUpperBound(var)) ||
                (is_coeff_pos && isModelStrictlyOverLowerBound(var))) {
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

LVRef Simplex::findNonBasicForPivotByBland(LVRef basicVar) {
    auto max_var_id = std::numeric_limits<unsigned>::max();
    LVRef y_found = LVRef_Undef;
    // Model doesn't fit the lower bound
    if (isModelOutOfLowerBound(basicVar)) {
        // For the Bland rule
        auto curr_var_id_y = max_var_id;
        // look for nonbasic terms to fix the breaking of the bound
        for (auto term : tableau.getRowPoly(basicVar)) {
            auto y = term.var;
            assert(basicVar != y);
            assert(tableau.isNonBasic(y));
            auto const &coeff = term.coeff;
            const bool coeff_is_pos = (coeff > 0);
            if ((coeff_is_pos && isModelStrictlyUnderUpperBound(y))
                || (!coeff_is_pos && isModelStrictlyOverLowerBound(y))) {
                // Choose the leftmost nonbasic variable with a negative (reduced) cost
                y_found = getVarId(y) < curr_var_id_y ? y : y_found;
                curr_var_id_y = getVarId(y) < curr_var_id_y ? getVarId(y) : curr_var_id_y;
            }
        }
    }
    else if (isModelOutOfUpperBound(basicVar)) {
        auto curr_var_id_y = max_var_id;
        // look for nonbasic terms to fix the unbounding
        for (auto term : tableau.getRowPoly(basicVar)) {
            auto y = term.var;
            assert(basicVar != y);
            assert(tableau.isNonBasic(y));
            auto const &coeff = term.coeff;
            const bool &coeff_is_pos = (coeff > 0);
            if ((!coeff_is_pos && isModelStrictlyUnderUpperBound(y))
                || (coeff_is_pos && isModelStrictlyOverLowerBound(y))) {
                // Choose the leftmost nonbasic variable with a negative (reduced) cost
                y_found = getVarId(y) < curr_var_id_y ? y : y_found;
                curr_var_id_y = getVarId(y) < curr_var_id_y ? getVarId(y) : curr_var_id_y;
            }
        }
    } else {
        opensmt_error("Error in bounds comparison");
    }
    return y_found;
}

Simplex::Explanation Simplex::assertBoundOnVar(LVRef it, LABoundRef itBound_ref) {
    assert(!model->isUnbounded(it));
    assert(boundStore[itBound_ref].getLVRef() == it);

    // Check if simple UNSAT can be given.  The last check checks that this is not actually about asserting equality.
    if (model->boundTriviallyUnsatisfied(it, itBound_ref)) {
        const LABound & itBound = boundStore[itBound_ref];
        assert(itBound.getType() == bound_u || itBound.getType() == bound_l);
        LABoundRef br = itBound.getType() == bound_u ? model->readLBoundRef(it) : model->readUBoundRef(it);
        return {{br, 1}, {itBound_ref, 1}};
    }

    // Here we count the bound as activated
    boundActivated(it);

    // Check if simple SAT can be given
    if (model->boundTriviallySatisfied(it, itBound_ref)) { return {}; }

    model->pushBound(itBound_ref);

    bufferOfActivatedBounds.emplace_back(it, itBound_ref);
    return {};
}

void Simplex::newCandidate(LVRef candidateVar) {
    assert(tableau.isBasic(candidateVar));
    candidates.insert(candidateVar);
}

void Simplex::eraseCandidate(LVRef candidateVar) {
    candidates.erase(candidateVar);
}


void Simplex::pivot(const LVRef bv, const LVRef nv){
    assert(tableau.isBasic(bv));
    assert(tableau.isNonBasic(nv));
    simplex_assert(valueConsistent(bv));
//    tableau.print();
    updateValues(bv, nv);
    tableau.pivot(bv, nv);
    // after pivot, bv is not longer a candidate
    eraseCandidate(bv);
    // and nv can be a candidate
    if (getNumOfBoundsActive(nv) == 0) {
        tableau.basicToQuasi(nv);
    }
    else {
        if (isModelOutOfBounds(nv)) {
            newCandidate(nv);
        }
    }
//    tableau.print();
    simplex_assert(checkTableauConsistency());
    simplex_assert(checkValueConsistency());
}

void Simplex::changeValueBy(LVRef var, const Delta & diff) {
    // update var's value
    model->write(var, model->read(var) + diff);
    // update all (active) rows where var is present
    for ( LVRef row : tableau.getColumn(var)){
        assert(!tableau.isNonBasic(row));
        if (tableau.isBasic(row)) { // skip quasi-basic variables
            model->write(row, model->read(row) + (tableau.getCoeff(row, var) * diff));
            if (isModelOutOfBounds(row)) {
                newCandidate(row);
            }
            else {
                eraseCandidate(row);
            }
        }
    }
}

void Simplex::updateValues(const LVRef bv, const LVRef nv){
    assert(isModelOutOfBounds(bv));
    auto bvNewVal = (isModelOutOfLowerBound(bv)) ? model->Lb(bv) : model->Ub(bv);
    const auto & coeff = tableau.getCoeff(bv, nv);
    // nvDiff represents how much we need to change nv, so that bv gets to the right value
    auto nvDiff = (bvNewVal - model->read(bv)) / coeff;
    // update nv's value
    changeValueBy(nv, nvDiff);
}

//
// Returns the bounds conflicting with the actual model.
//
Simplex::Explanation Simplex::getConflictingBounds(LVRef x, bool conflictOnLower)
{
    LABoundRef br_f = conflictOnLower ? model->readLBoundRef(x) : model->readUBoundRef(x);
    Explanation expl = {{br_f,1}};
    // add all bounds for polynomial elements which limit the given bound
    for (auto const & term : tableau.getRowPoly(x)) {
        Real const & coeff = term.coeff;
        auto const var = term.var;
        assert(!coeff.isZero() && var != x);
        if (coeff < 0) {
            LABoundRef br = conflictOnLower ? model->readLBoundRef(var) : model->readUBoundRef(var);
            expl.push_back({br, -coeff});
        }
        else {
            LABoundRef br = conflictOnLower ? model->readUBoundRef(var) : model->readLBoundRef(var);
            expl.push_back({br, coeff});
        }
    }
    return expl;
}

bool Simplex::checkValueConsistency() const {
    bool res = true;
    auto const & rows = tableau.getRows();
    for (unsigned i = 0; i < rows.size(); ++i) {
        if (!rows[i]) { continue; }
        LVRef var {i};
        assert(!tableau.isNonBasic(var));
        if (tableau.isBasic(var)) {
            res &= valueConsistent(var);
        }
    }
    assert(res);
    return res;
}

bool Simplex::valueConsistent(LVRef v) const
{
    const Delta& value = model->read(v);
    Delta sum(0);
    for (auto & term : tableau.getRowPoly(v)){
#ifdef TRACE_VALUE_CONSISTENT
        cout << sum << " += " << term.coeff << " * " << model->read(term.var) << endl;
#endif
        sum += term.coeff * model->read(term.var);
#ifdef TRACE_VALUE_CONSISTENT
        cout << " => " << sum << endl;
#endif
    }

    assert(value == sum);
    return value == sum;
}


bool Simplex::invariantHolds() const
{
    bool rval = true;
    auto vars = tableau.getNonBasicVars();
    for (auto var : vars){
        if (isModelOutOfBounds(var)) {
            rval = false;
            if (isModelOutOfUpperBound(var)) {
                printf("Non-basic (column) LRA var %s has value %s <= %s \n",
                       printVar(var), model->read(var).printValue(), model->Ub(var).printValue());
            }
            if (isModelOutOfLowerBound(var)) {
                printf("Non-basic (column) LRA var %s has value %s <= %s \n",
                       printVar(var), model->Lb(var).printValue(), model->read(var).printValue());
            }
            assert(false);
        }
    }
    return rval;
}


bool Simplex::checkTableauConsistency() const {
    bool res = tableau.checkConsistency();
    assert(res);
    return res;
}

bool Simplex::isProcessedByTableau(LVRef var) const { return tableau.isProcessed(var); }

const LABoundRef Simplex::getBound(LVRef v, int idx) const { return boundStore.getBoundByIdx(v, idx); }

Delta Simplex::getValuation(LVRef v) const {
    if (tableau.isQuasiBasic(v)) {
        (const_cast<Simplex*>(this))->quasiToBasic(v);
    }
    Delta val = model->read(v);
    return val;
}

opensmt::Real Simplex::computeDelta() const {

    /*
     Delta computation according to the Technical Report accompanying the Simple paper
     https://yices.csl.sri.com/papers/sri-csl-06-01.pdf
     For a pair (c,k) \in Q_\delta representing Real value c + k * \delta if the inequality (c_1, k_1) <= (c_2, k_2) holds
     then there exists \delta_0 such that \forall 0 < \epsilon < \delta_0 the inequality c_1 + k_1 * \epsilon <= c_2 + k_2 * \epsilon holds.

     \delta_0 can be defined as (c_2 - c_1) / (k_1 - k_2) if c_1 < c_2 and k_1 > k_2 ( and \delta_0 = 1 otherwise)

     Extending to a set of inequilities, we can take minimum of deltas needed to satisfy every inequality separately

     In our case, for each variable we need to consider both lower and upper bound (if they exist)
    */

    Delta delta_abst;
    bool deltaNotSet = true;

    const LAVarStore& laVarStore = boundStore.getVarStore();
    for (LVRef v : laVarStore)
    {
        assert( !isModelOutOfBounds(v) );

        if (model->read(v).D() == 0)
            continue; // If values are exact we do not need to consider them for delta computation

        auto const & val = model->read(v);
        // Computing delta to satisfy lower bound
        if (model->hasLBound(v)) {
            auto const & lb = model->Lb(v);
            assert(lb.R() <= val.R());
            if (lb.R() < val.R() && lb.D() > val.D()) {
                Real valOfDelta = (val.R() - lb.R()) / (lb.D() - val.D());
                assert(valOfDelta > 0);
                if (deltaNotSet || delta_abst > valOfDelta) {
                    deltaNotSet = false;
                    delta_abst = valOfDelta;
                }
            }
        }
        // Computing delta to satisfy upper bound
        if (model->hasUBound(v)) {
            auto const & ub = model->Ub(v);
            assert(ub.R() >= val.R());
            if (val.R() < ub.R() && val.D() > ub.D()) {
                Real valOfDelta = (ub.R() - val.R()) / (val.D() - ub.D());
                assert(valOfDelta > 0);
                if (deltaNotSet || delta_abst > valOfDelta) {
                    deltaNotSet = false;
                    delta_abst = valOfDelta;
                }
            }
        }
    }

    if (deltaNotSet || delta_abst > 1) {
        return 1;
    }
    return delta_abst.R()/2;
}

void Simplex::quasiToBasic(LVRef it) {
    tableau.quasiToBasic(it);
    // Recompute the value of the row variable
    // Literals are asserted in groups, so the current assignment might already be different then the last consistent one
    // Fix the last consistent value for this var, then fix the current value of the var
    Delta val; // initialized to 0
    assert(model->changed_vars_vec.size() == 0);
    for (auto const & term : tableau.getRowPoly(it)) {
        assert(model->read(term.var) == model->readBackupValue(term.var));
        val += term.coeff * model->read(term.var);
    }
    model->restoreVarWithValue(it, std::move(val));
}

Simplex::~Simplex()
{
#ifdef STATISTICS
     simplex_stats.printStatistics(cerr);
#endif // STATISTICS
}

void Simplex::processBufferOfActivatedBounds() {
    while (!bufferOfActivatedBounds.empty()) {
        LVRef var = bufferOfActivatedBounds.back().first;
        LABoundRef boundRef = bufferOfActivatedBounds.back().second;
        bufferOfActivatedBounds.pop_back();
        assert(!tableau.isQuasiBasic(var));
        // Update the Tableau data if a non-basic variable
        if (tableau.isNonBasic(var)) {
            auto const & bound = boundStore[boundRef];
            if (!isBoundSatisfied(model->read(var), bound)) {
                changeValueBy(var, bound.getValue() - model->read(var));
            }
        } else // basic variable got a new bound, it becomes a possible candidate
        {
            assert(tableau.isBasic(var));
            if (isModelOutOfBounds(var)) {
                newCandidate(var);
            } else {
                // MB: Experience shows this should really not happen
                assert(candidates.find(var) == candidates.end());
            }
        }
    }
}

