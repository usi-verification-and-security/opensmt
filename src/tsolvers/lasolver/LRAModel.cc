//
// Created by prova on 04.01.18.
//

#include "LRAModel.h"

void LRAModel::init()
{
    LAVarStore const & varStore = bs.getVarStore();
    for (LVRef ref : varStore) {
        addVar(ref);
    }
}

int
LRAModel::addVar(LVRef v)
{
    if (has_model.has(v))
        return n_vars_with_model;

    while (static_cast<unsigned>(current_assignment.size()) <= getVarId(v)) {
        current_assignment.emplace_back();
        last_consistent_assignment.emplace_back();
        changed_vars_set.assure_domain(getVarId(v));
        int_lbounds.emplace_back();
        int_ubounds.emplace_back();
    }

    has_model.insert(v, true);
    return ++n_vars_with_model;
}

void
LRAModel::write(const LVRef &v, Delta val)
{
    current_assignment[getVarId(v)] = std::move(val);
    if (!changed_vars_set.contains(getVarId(v))) {
        changed_vars_set.insert(getVarId(v));
        changed_vars_vec.push(v);
    }
}


void
LRAModel::pushBound(const LABoundRef br) {
    LABound& b = bs[br];
    LVRef vr = b.getLVRef();
    if (b.getType() == bound_u) {
        int_ubounds[getVarId(vr)].push(br);
    }
    else {
        int_lbounds[getVarId(vr)].push(br);
    }

    bound_trace.push(br);
}

void
LRAModel::popBounds()
{
    for (int i = bound_trace.size()-1; i >= bound_limits.last(); i--) {
        LABoundRef br = bound_trace[i];
        LABound &b = bs[br];
        LVRef vr = b.getLVRef();
        if (b.getType() == bound_u) {
            int_ubounds[getVarId(vr)].pop();
        } else {
            int_lbounds[getVarId(vr)].pop();
        }
    }
    bound_trace.shrink(bound_trace.size() - bound_limits.last());
}

void LRAModel::clear() {
    this->current_assignment.clear();
    this->last_consistent_assignment.clear();
    this->changed_vars_set.reset();
    this->changed_vars_vec.clear();
    this->int_lbounds.clear();
    this->bound_trace.clear();
    this->has_model.clear();
    this->int_ubounds.clear();
    this->bound_limits.clear();
    this->n_vars_with_model = 0;

    bound_limits.push(0);
}

bool LRAModel::verifyProperlyBacktracked() const {
    bool ok = true;
    ok &= std::all_of(int_lbounds.begin(), int_lbounds.end(), [](auto const& elem) { return elem.size() == 0;});
    ok &= std::all_of(int_ubounds.begin(), int_ubounds.end(), [](auto const& elem) { return elem.size() == 0;});
    ok &= changed_vars_vec.size() == 0;
    ok &= changed_vars_set.empty();
    ok &= bound_trace.size() == 0;
    ok &= bound_limits.size() == 1;
    return ok;
}

int LRAModel::backtrackLevel() { return bound_limits.size() - 1; }


LABoundRef LRAModel::readLBoundRef(LVRef v) const { assert(hasLBound(v)); return int_lbounds[getVarId(v)].last(); }
const LABound& LRAModel::readLBound(const LVRef &v) const { return bs[readLBoundRef(v)]; }
LABoundRef LRAModel::readUBoundRef(LVRef v) const { assert(hasUBound(v)); return int_ubounds[getVarId(v)].last(); }
const LABound& LRAModel::readUBound(const LVRef &v) const { return bs[readUBoundRef(v)]; }
void LRAModel::pushBacktrackPoint()      { bound_limits.push(bound_trace.size()); }
void LRAModel::popBacktrackPoint() { popBounds(); bound_limits.pop(); }; // Returns the decision if the backtrack point had a decision
int  LRAModel::getBacktrackSize() const { return bound_limits.size(); }

bool LRAModel::isEquality(LVRef v) const {
    return hasLBound(v) && hasUBound(v)
        && bs[int_lbounds[getVarId(v)].last()].getIdx().x+1 == bs[int_ubounds[getVarId(v)].last()].getIdx().x
        && Lb(v) == Ub(v);
}
bool LRAModel::isUnbounded(LVRef v) const { return bs.isUnbounded(v); }
bool LRAModel::boundTriviallySatisfied(LVRef v, LABoundRef b) const
{
    const LABound& bound = bs[b];
    assert(bound.getType() == bound_l || bound.getType() == bound_u);
    const bool is_lower = bound.getType() == bound_l;
    if ((is_lower && !hasLBound(v)) || (!is_lower && !hasUBound(v))) { return false; }
    const LABound& toCompare = is_lower ? readLBound(v) : readUBound(v);
    return ((!is_lower && bound.getIdx().x >= toCompare.getIdx().x) || (is_lower && bound.getIdx().x <= toCompare.getIdx().x));
}
bool LRAModel::boundTriviallyUnsatisfied(LVRef v, LABoundRef b) const
{
    const LABound& bound = bs[b];
    assert(bound.getType() == bound_l || bound.getType() == bound_u);
    const bool is_lower = bound.getType() == bound_l;
    if ((is_lower && !hasUBound(v)) || (!is_lower && !hasLBound(v))) { return false; }
    const LABound& toCompare = is_lower ? readUBound(v) : readLBound(v);
    return (is_lower ? bound.getIdx().x > toCompare.getIdx().x : bound.getIdx().x < toCompare.getIdx().x)
            && bound.getValue() != toCompare.getValue();

}