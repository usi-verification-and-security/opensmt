//
// Created by prova on 06.09.19.
//

#include "Simplex.h"

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

    bool bland_rule = false;
    unsigned repeats = 0;
    // These values are from Yices
    unsigned bthreshold = bland_threshold;
    if (boundStore.nVars() > 10000)
        bthreshold *= 1000;
    else if (boundStore.nVars() > 1000)
        bthreshold *= 100;

    // keep doing pivotAndUpdate until the SAT/UNSAT status is confirmed
    while (true) {
        repeats++;
        LVRef x = LVRef_Undef;

        if (!bland_rule && (repeats > bthreshold))
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
            return getConflictingBounds(x);
        }
            // if it was found - pivot old Basic x with non-basic y and do the model updates
        else {
            pivot(x, y_found);
        }
    }
}

bool Simplex::isModelOutOfBounds(LVRef v) const {
    return ( (model->read(v) > model->Ub(v)) || (model->read(v) < model->Lb(v)) );
}

bool Simplex::isModelOutOfUpperBound(LVRef v) const
{
    return ( model->read(v)> model->Ub(v) );
}

bool Simplex::isModelOutOfLowerBound(LVRef v) const
{
    return ( model->read(v) < model->Lb(v) );
}

const Delta Simplex::overBound(LVRef v) const
{
    assert( isModelOutOfBounds(v) );
    if (isModelOutOfUpperBound(v))
    {
        return ( Delta(model->read(v) - model->Ub(v)) );
    }
    else if ( isModelOutOfLowerBound(v) )
    {
        return ( Delta(model->Lb(v) - model->read(v)) );
    }
    assert (false);
    printf("Problem in overBound, LRASolver.C:%d\n", __LINE__);
    exit(1);
}

bool Simplex::isEquality(LVRef v) const
{
    return model->isEquality(v);
}

bool Simplex::isUnbounded(LVRef v) const
{
    bool rval = model->isUnbounded(v);
//    if (rval)
//        printf("Var %s is unbounded\n", lva.printVar(v));
    return rval;
}

LVRef Simplex::getBasicVarToFixByShortestPoly() const {
    decltype(candidates) new_candidates;
    LVRef current = LVRef_Undef;
    std::size_t current_poly_size = static_cast<std::size_t>(-1);
    for (auto it : candidates) {
        assert(tableau.isBasic(it));
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

LVRef Simplex::getBasicVarToFixByBland() const {
    decltype(candidates) new_candidates;
    int curr_var_id_x = boundStore.nVars();
    LVRef current = LVRef_Undef;
    for (auto it : candidates) {
        assert(it != LVRef_Undef);
        assert(tableau.isBasic(it));
        if (isModelOutOfBounds(it)) {
            new_candidates.insert(it);
            // Select the var with the smallest id
            auto id = getVarId(it);
            assert(it.x == id);
            current = id < curr_var_id_x ? it : current;
            curr_var_id_x = id < curr_var_id_x ? id : curr_var_id_x;
        }
    }
    candidates.swap(new_candidates);
    return current;
}

LVRef Simplex::findNonBasicForPivotByHeuristic(LVRef basicVar) {
    // favor more independent variables: those present in less rows
    assert(tableau.isBasic(basicVar));
    LVRef v_found = LVRef_Undef;
    if (model->read(basicVar) < model->Lb(basicVar)) {

        for (auto const &term : tableau.getRowPoly(basicVar)) {
            auto var = term.var;
            assert(tableau.isNonBasic(var));
            assert(var != basicVar);
            auto const &coeff = term.coeff;
            const bool is_coeff_pos = coeff > 0;

            if ((is_coeff_pos && model->read(var) < model->Ub(var)) ||
                (!is_coeff_pos && model->read(var) > model->Lb(var))) {
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
    else if (model->read(basicVar) > model->Ub(basicVar)) {

        for (auto const &term : tableau.getRowPoly(basicVar)) {
            auto var = term.var;
            assert(tableau.isNonBasic(var));
            assert(var != basicVar);
            auto const &coeff = term.coeff;
            const bool is_coeff_pos = coeff > 0;

            if ((!is_coeff_pos && model->read(var) < model->Ub(var)) ||
                (is_coeff_pos && model->read(var) > model->Lb(var))) {
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
    int max_var_id = boundStore.nVars();
    LVRef y_found = LVRef_Undef;
    // Model doesn't fit the lower bound
    if (model->read(basicVar) < model->Lb(basicVar)) {
        // For the Bland rule
        int curr_var_id_y = max_var_id;
        // look for nonbasic terms to fix the breaking of the bound
        for (auto term : tableau.getRowPoly(basicVar)) {
            auto y = term.var;
            assert(basicVar != y);
            assert(tableau.isNonBasic(y));
            auto const &coeff = term.coeff;
            const bool coeff_is_pos = (coeff > 0);
            if ((coeff_is_pos && model->read(y) < model->Ub(y)) || (!coeff_is_pos && model->read(y) > model->Lb(y))) {
                // Choose the leftmost nonbasic variable with a negative (reduced) cost
                y_found = getVarId(y) < curr_var_id_y ? y : y_found;
                curr_var_id_y = getVarId(y) < curr_var_id_y ? getVarId(y) : curr_var_id_y;
            }
        }
    }
    else if (model->read(basicVar) > model->Ub(basicVar)) {
        int curr_var_id_y = max_var_id;
        // look for nonbasic terms to fix the unbounding
        for (auto term : tableau.getRowPoly(basicVar)) {
            auto y = term.var;
            assert(basicVar != y);
            assert(tableau.isNonBasic(y));
            auto const &coeff = term.coeff;
            const bool &coeff_is_pos = (coeff > 0);
            if ((!coeff_is_pos && model->read(y) < model->Ub(y)) || (coeff_is_pos && model->read(y) > model->Lb(y))) {
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
    const LABound &itBound = boundStore[itBound_ref];

//  cerr << "; ASSERTING bound on " << *it << endl;


    // Check if simple UNSAT can be given.  The last check checks that this is not actually about asserting equality.
    if (model->boundUnsatisfied(it, itBound_ref))
    {
        LABoundRef br = itBound.getType() == bound_u ? model->readLBoundRef(it) : model->readUBoundRef(it);
        return {{br, 1}, {itBound_ref, 1}};
    }

    // Check if simple SAT can be given
    if (model->boundSatisfied(it, itBound_ref))
        return {};

    model->pushBound(itBound_ref);

    // Update the Tableau data if a non-basic variable
    if (tableau.isNonBasic(it)) {
        if (!isBoundSatisfied(model->read(it), itBound)) {
            changeValueBy(it, itBound.getValue() - model->read(it));
        }
    }
    else // basic variable got a new bound, it becomes a possible candidate
    {
        if(!tableau.isActive(it)) {
            throw "Not implemented yet!";
        }
        assert(tableau.isBasic(it));
        newCandidate(it);
    }

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
    assert(valueConsistent(bv));
//    tableau.print();
    updateValues(bv, nv);
    tableau.pivot(bv, nv);
    // after pivot, bv is not longer a candidate
    eraseCandidate(bv);
    // and nv can be a candidate
    newCandidate(nv);
//    tableau.print();
    assert(checkTableauConsistency());
    assert(checkValueConsistency());
}

void Simplex::changeValueBy(LVRef var, const Delta & diff) {
    // update var's value
    model->write(var, model->read(var) + diff);
    // update all (active) rows where var is present
    for ( LVRef row : tableau.getColumn(var)){
        assert(tableau.isBasic(row));
        if (tableau.isActive(row)) {
            model->write(row, model->read(row) + (tableau.getCoeff(row, var) * diff));
            newCandidate(row);
        }
    }
}

void Simplex::updateValues(const LVRef bv, const LVRef nv){
    assert(model->read(bv) < model->Lb(bv) || model->read(bv) > model->Ub(bv));
    auto bvNewVal = (model->read(bv) < model->Lb(bv)) ? model->Lb(bv) : model->Ub(bv);
    const auto & coeff = tableau.getCoeff(bv, nv);
    // nvDiff represents how much we need to change nv, so that bv gets to the right value
    auto nvDiff = (bvNewVal - model->read(bv)) / coeff;
    // update nv's value
    changeValueBy(nv, nvDiff);
}

//
// Returns the bounds conflicting with the actual model.
//
Simplex::Explanation Simplex::getConflictingBounds(LVRef x)
{
    Explanation expl;
    if (model->read(x) < model->Lb(x)) {
        // add all bounds for polynomial elements which limit lower bound
        LABoundRef b_f = model->readLBoundRef(x);
        expl.push_back({b_f, 1});
        for (auto const & term : tableau.getRowPoly(x)) {
            Real const & coeff = term.coeff;
            assert(! coeff.isZero());
            auto const var = term.var;
            assert(var != x);
            if (coeff < 0) {
                LABoundRef br = model->readLBoundRef(var);
                expl.push_back({br, -coeff});
            }
            else {
                LABoundRef br = model->readUBoundRef(var);
                expl.push_back({br,coeff});
            }
        }
    }
    if (model->read(x) > model->Ub(x)) {
        // add all bounds for polynomial elements which limit upper bound
        LABoundRef br_f = model->readUBoundRef(x);
        expl.push_back({br_f,1});

        for (auto const & term : tableau.getRowPoly(x)) {
            Real const & coeff = term.coeff;
            assert( ! coeff.isZero());
            auto const var = term.var;
            assert(var != x);
            if (coeff > 0) {
                LABoundRef br = model->readLBoundRef(var);
                expl.push_back({br, coeff});
            }
            else {
                LABoundRef br = model->readUBoundRef(var);
                expl.push_back({br, -coeff});
            }
        }
    }
    return expl;
}

bool Simplex::checkValueConsistency() const {
    bool res = true;
    auto const & rows = tableau.getRows();
    for(unsigned i = 0; i < rows.size(); ++i) {
        if(!rows[i]) {continue;}
        LVRef var {i};
        if(tableau.isActive(var)){
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
      sum += term.coeff * model->read(term.var);
    }

    assert(value == sum);
    return value == sum;
}


bool Simplex::invariantHolds() const
{
    bool rval = true;
    for (auto var : tableau.getNonBasicVars()){
        assert(model->hasModel(var));
        if (isModelOutOfBounds(var)) {
            rval = false;
            printf("Non-basic (column) LRA var %s has value %s <= %s <= %s\n",
                   printVar(var), model->Lb(var).printValue(),
                   model->read(var).printValue(), model->Ub(var).printValue());
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

bool Simplex::isProcessedByTableau(LVRef var) const {return tableau.isProcessed(var);}

const LABoundRef Simplex::getBound(LVRef v, int idx) const { return boundStore.getBoundByIdx(v, idx); }

void Simplex::doGaussianElimination( )
{
    auto eliminated = tableau.doGaussianElimination([this](LVRef v){return this->isUnbounded(v);});
    for(auto rit = eliminated.rbegin(); rit != eliminated.rend(); ++ rit) {
        auto entry = *rit;
        auto poly = entry.second;
        for(auto const & term : entry.second){
            auto var = term.var;
            auto it = removed_by_GaussianElimination.find(var);
            if( it != removed_by_GaussianElimination.end() && poly.contains(var)) {
                auto to_substitute = (*it).second;
                auto coeff = poly.getCoeff(var);
                poly.merge(to_substitute, coeff);
            }
        }
        removed_by_GaussianElimination.emplace(entry.first, poly);
    }
}

Delta Simplex::getValuation(LVRef v) const {
    Delta val(0);
    if (isRemovedByGaussianElimination(v)) {
        auto it = getRemovedByGaussianElimination(v);
        auto const & representation = (*it).second;

        for (auto const & term : representation) {
            val += term.coeff * model->read(term.var);
        }
    }
    else {
        val = model->read(v);
    }
    return val;
}

opensmt::Real Simplex::computeDelta() const {


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

    Delta delta_abst = Delta_PlusInf;

    for (unsigned i = 0; i < boundStore.nVars(); ++i)
    {
        LVRef v {i};
        if (model->read(v).D() == 0)
            continue; // If values are exact we do not need to consider them for delta computation

        assert( !isModelOutOfBounds(v) );

        Delta D;

        if (model->Lb(v).isMinusInf() || model->Ub(v).isPlusInf())
            D = Delta_PlusInf;
        else
            D = (model->Lb(v).R() + model->Ub(v).R())/2 - model->read(v).R();

        D = D/model->read(v).D();

        if (D < 0) D.negate();

        if (delta_abst > D)
            delta_abst = D;
    }

    if (delta_abst.isPlusInf())
        return 1;
    else
        return delta_abst.R();
}

Simplex::~Simplex()
{
#ifdef STATISTICS
     simplex_stats.printStatistics(cerr);
#endif // STATISTICS
}

