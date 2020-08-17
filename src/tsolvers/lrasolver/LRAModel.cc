//
// Created by prova on 04.01.18.
//

#include "LRAModel.h"
#include "LRALogic.h"

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
        current_assignment.push();
        last_consistent_assignment.push();
        changed_vars_set.assure_domain(getVarId(v));
        int_lbounds.push();
        int_ubounds.push();
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
    LABound const & b = bs[br];
    LVRef vr = b.getLVRef();
    if (b.getType() == bound_u) {
        int_ubounds[getVarId(vr)].push(br);
    }
    else {
        int_lbounds[getVarId(vr)].push(br);
    }
}

void LRAModel::popBound(LVRef var, BoundT type) {
    if (type == bound_u) {
        int_ubounds[getVarId(var)].pop();
    } else {
        int_lbounds[getVarId(var)].pop();
    }
}

void LRAModel::clear() {
    this->current_assignment.clear();
    this->last_consistent_assignment.clear();
    this->changed_vars_set.reset();
    this->changed_vars_vec.clear();
    this->int_lbounds.clear();
    this->has_model.clear();
    this->int_ubounds.clear();
    this->n_vars_with_model = 0;

}

LABoundRef LRAModel::readLBoundRef(LVRef v) const { assert(hasLBound(v)); return int_lbounds[getVarId(v)].last(); }
const LABound& LRAModel::readLBound(const LVRef &v) const { return bs[readLBoundRef(v)]; }
LABoundRef LRAModel::readUBoundRef(LVRef v) const { assert(hasUBound(v)); return int_ubounds[getVarId(v)].last(); }
const LABound& LRAModel::readUBound(const LVRef &v) const { return bs[readUBoundRef(v)]; }


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