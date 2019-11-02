//
// Created by prova on 04.01.18.
//

#include "LRAModel.h"
#include "LRALogic.h"

void LRAModel::init()
{
    for (unsigned i = 0; i < bs.nVars(); i++) {
        LVRef ref {i};
        addVar(ref);
    }
}

int
LRAModel::addVar(LVRef v)
{
    if (has_model.has(v))
        return n_vars_with_model;

    while (current_assignment.size() <= getVarId(v)) {
        current_assignment.push();
        last_consistent_assignment.push();
        changed_vars_set.assure_domain(getVarId(v));
        int_lbounds.push();
        int_ubounds.push();
    }

    has_model.insert(v, true);
    int_lbounds[getVarId(v)].push({ bs.getBoundByIdx(v, 0), 0 });
    int_ubounds[getVarId(v)].push({ bs.getBoundByIdx(v, bs.getBoundListSize(v)-1), 0 });
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
        int_ubounds[getVarId(vr)].push({br, backtrackLevel()});
    }
    else
        int_lbounds[getVarId(vr)].push({br, backtrackLevel()});

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
    this->changed_vars_vec.reset();
    this->int_lbounds.clear();
    this->bound_trace.clear();
    this->has_model.clear();
    this->int_ubounds.clear();
    this->bound_limits.clear();
    this->n_vars_with_model = 0;

    bound_limits.push(0);
}

int LRAModel::backtrackLevel() { return bound_limits.size() - 1; }

LABoundRef LRAModel::readLBoundRef(LVRef v) const { return int_lbounds[getVarId(v)].last().br; }
const LABound& LRAModel::readLBound(const LVRef &v) const { return bs[readLBoundRef(v)]; }
LABoundRef LRAModel::readUBoundRef(LVRef v) const { return int_ubounds[getVarId(v)].last().br; }
const LABound& LRAModel::readUBound(const LVRef &v) const { return bs[readUBoundRef(v)]; }
const Delta& LRAModel::Lb(LVRef v) const { return bs[int_lbounds[getVarId(v)].last().br].getValue(); }
const Delta& LRAModel::Ub(LVRef v) const { return bs[int_ubounds[getVarId(v)].last().br].getValue(); }
void LRAModel::pushBacktrackPoint()      { bound_limits.push(bound_trace.size()); }
void LRAModel::popBacktrackPoint() { popBounds(); bound_limits.pop(); }; // Returns the decision if the backtrack point had a decision
int  LRAModel::getBacktrackSize() const { return bound_limits.size(); }

bool LRAModel::isEquality(LVRef v) const { return bs[int_lbounds[getVarId(v)].last().br].getIdx().x+1 == bs[int_ubounds[getVarId(v)].last().br].getIdx().x && !Lb(v).isInf() && !Ub(v).isInf() && Lb(v) == Ub(v); }
bool LRAModel::isUnbounded(LVRef v) const { return bs.isUnbounded(v); }
bool LRAModel::boundSatisfied(LVRef v, LABoundRef b) const { return ((bs[b].getType() == bound_u) && bs[b].getIdx().x >= readUBound(v).getIdx().x) || ((bs[b].getType() == bound_l) && bs[b].getIdx().x <= readLBound(v).getIdx().x); }
bool LRAModel::boundUnsatisfied(LVRef v, LABoundRef b) const
{
    // return ((bs[b].getType() == bound_l) && (bs[b].getIdx().x > readUBound(v).getIdx().x && bs[b].getValue() != Ub(v))) ||
    //     ((bs[b].getType() == bound_u) && (bs[b].getIdx().x < readLBound(v).getIdx().x && bs[b].getValue() != Lb(v)));
    const LABound& bound = bs[b];
    assert(bound.getType() == bound_l || bound.getType() == bound_u);
    bool is_lower = bound.getType() == bound_l;
    const LABound& toCompare = is_lower ? readUBound(v) : readLBound(v);
    return (is_lower ? bound.getIdx().x > toCompare.getIdx().x : bound.getIdx().x < toCompare.getIdx().x)
            && bound.getValue() != toCompare.getValue();

}