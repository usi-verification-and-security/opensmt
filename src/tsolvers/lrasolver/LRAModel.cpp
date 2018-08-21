//
// Created by prova on 04.01.18.
//

#include "LRAModel.h"
#include "LRALogic.h"

void LRAModel::initModel(LAVarStore &s)
{
    for (int i = 0; i < s.numVars(); i++)
        addVar(s.getVarByIdx(i));
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
//    printf("Pushing the default model for %s\n", lva.printVar(v));
    write(v, Delta());
    int_lbounds[lva[v].ID()].push({ bs.getBoundByIdx(v, 0), 0 });
    int_ubounds[lva[v].ID()].push({ bs.getBoundByIdx(v, bs.getBoundListSize(v)-1), 0 });
    return ++n_vars_with_model;
}

//void
//LRAModel::write(const LVRef &v, const Delta& val)
//{
//    if ((int_model[lva[v].ID()].size() == 0) || (int_model[lva[v].ID()].last().dl != backtrackLevel())) {
//        int_model[lva[v].ID()].push();
//        model_trace.push(v);
//    }
//    ModelEl& el = int_model[lva[v].ID()].last();
//    el.d  = val;
//    el.dl = backtrackLevel();
//}

void
LRAModel::write(const LVRef &v, Delta val)
{
    if ((int_model[lva[v].ID()].size() == 0) || (int_model[lva[v].ID()].last().dl != backtrackLevel())) {
        int_model[lva[v].ID()].push();
        model_trace.push(v);
    }
    ModelEl& el = int_model[lva[v].ID()].last();
    el.d  = std::move(val);
    el.dl = backtrackLevel();
}

void
LRAModel::pushDecision(PtAsgn asgn)
{
    int_decisions.push({asgn, backtrackLevel()});
    decision_trace.push(asgn);
}

void
LRAModel::pushBound(const LABoundRef br) {
    LABound& b = bs[br];
    LVRef vr = b.getLVRef();
    if (b.getType() == bound_u) {
        int_ubounds[lva[vr].ID()].push({br, backtrackLevel()});
    }
    else
        int_lbounds[lva[vr].ID()].push({br, backtrackLevel()});

    bound_trace.push(br);
}

void
LRAModel::popBounds()
{
    for (int i = bound_trace.size()-1; i >= limits.last().bound_lim; i--) {
        LABoundRef br = bound_trace[i];
        LABound &b = bs[br];
        LVRef vr = b.getLVRef();
        LABoundRef latest_bound = LABoundRef_Undef;
        if (b.getType() == bound_u) {
            int_ubounds[lva[vr].ID()].pop();
        } else {
            int_lbounds[lva[vr].ID()].pop();
        }
    }
    bound_trace.shrink(bound_trace.size() - limits.last().bound_lim);
}

void
LRAModel::popModels()
{
    assert(limits.size() > 0);
    for (int i = model_trace.size()-1; i >= limits.last().model_lim; i--) {
        int id = lva[model_trace[i]].ID();
        if (int_model[id].size() == 1) {
            ModelEl& m = int_model[id][0];
            m.d.reset();
            m.dl = 0;
        } else {
            int_model[lva[model_trace[i]].ID()].pop();
        }
    }
    model_trace.shrink(model_trace.size() - limits.last().model_lim);
}

PtAsgn
LRAModel::popDecisions()
{
    assert(limits.size() > 0);
    assert((decision_trace.size() - limits.last().dec_lim == 0) || (decision_trace.size() - limits.last().dec_lim == 1));
    PtAsgn popd = PtAsgn_Undef;
    if (decision_trace.size()-limits.last().dec_lim == 1) {
        popd = int_decisions.last().asgn;
        int_decisions.pop();
    }
    decision_trace.shrink(decision_trace.size() - limits.last().dec_lim);
    return popd;
}



void LRAModel::printModelState()
{
    printf("We have %d backtrack points\n", getBacktrackSize());
    vec<LVRef> vars;
    has_model.getKeys(vars);
    for (int i = 0; i < vars.size(); i++) {
        LVRef v = vars[i];
        if (has_model[v]) {
            int id = lva[v].ID();
            vec<ModelEl> &vals = int_model[id];
            printf("Var %s [%s], has %d models\n", lva.printVar(v), logic.pp(lva[v].getPTRef()), vals.size());
            char *buf = (char*) malloc(1);
            buf[0] = '\0';
            for (int j = 0; j < vals.size(); j++) {
                char *tmp_buf;
                asprintf(&tmp_buf, "%s(%s, %d) ", buf, vals[j].d.printValue(), vals[j].dl);
                free(buf);
                buf = tmp_buf;
            }
            printf(" - %s\n", buf);
            free(buf);
        }
        else
            printf("Var %s has no models\n", lva.printVar(v));
    }
    printf("There are %d bounds in the bound trace\n", bound_trace.size());
    for (int i = 0; i < bound_trace.size(); i++) {
        LABoundRef br = bound_trace[i];
        char* str = bs.printBound(br);
        printf(" - %s\n", str);
        free(str);
    }
}

void LRAModel::clear() {
    this->int_model.clear();
    this->int_lbounds.clear();
    this->bound_trace.clear();
    this->decision_trace.clear();
    this->has_model.clear();
    this->int_decisions.clear();
    this->int_ubounds.clear();
    this->limits.clear();
    this->model_trace.clear();
    this->n_vars_with_model = 0;

    limits.push({0, 0});
}

int LRAModel::backtrackLevel() { return limits.size() - 1; }

//inline const Delta& LRAModel::read (const LVRef &v) const { assert(hasModel(v)); return int_model[lva[v].ID()].last().d; }
const  bool  LRAModel::hasModel(const LVRef& v) const { return (lva[v].ID() < int_model.size() && int_model[lva[v].ID()].size() > 0); }

const LABound& LRAModel::readLBound(const LVRef &v) const { return bs[int_lbounds[lva[v].ID()].last().br]; }
const LABound& LRAModel::readUBound(const LVRef &v) const { return bs[int_ubounds[lva[v].ID()].last().br]; }
const Delta& LRAModel::Lb(LVRef v) const { return bs[int_lbounds[lva[v].ID()].last().br].getValue(); }
const Delta& LRAModel::Ub(LVRef v) const { return bs[int_ubounds[lva[v].ID()].last().br].getValue(); }
void LRAModel::pushBacktrackPoint()      { limits.push({model_trace.size(), bound_trace.size(), decision_trace.size()}); }
PtAsgn LRAModel::popBacktrackPoint() { popModels(); popBounds(); PtAsgn popd = popDecisions(); limits.pop(); return popd; }; // Returns the decision if the backtrack point had a decision
int  LRAModel::getBacktrackSize() const { return limits.size(); }

bool LRAModel::isEquality(LVRef v) const { return bs[int_lbounds[lva[v].ID()].last().br].getIdx()+1 == bs[int_ubounds[lva[v].ID()].last().br].getIdx() && !Lb(v).isInf() && !Ub(v).isInf() && Lb(v) == Ub(v); }
bool LRAModel::isUnbounded(LVRef v) const { return bs.isUnbounded(v); }
bool LRAModel::boundSatisfied(LVRef v, LABoundRef b) const { return ((bs[b].getType() == bound_u) && !(bs[b].getIdx() < readUBound(v).getIdx())) || ((bs[b].getType() == bound_l) && !(bs[b].getIdx() > readLBound(v).getIdx())); }
bool LRAModel::boundUnsatisfied(LVRef v, LABoundRef b) const
{ return ((bs[b].getType() == bound_l) && (bs[b].getIdx() > readUBound(v).getIdx() && bs[b].getValue() != Ub(v))) ||
         ((bs[b].getType() == bound_u) && (bs[b].getIdx() < readLBound(v).getIdx() && bs[b].getValue() != Lb(v))); }