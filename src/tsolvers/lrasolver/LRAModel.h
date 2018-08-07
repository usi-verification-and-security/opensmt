//
// Created by prova on 04.01.18.
//

#ifndef OPENSMT_LRAMODEL_H
#define OPENSMT_LRAMODEL_H

#include <cstdint>
#include "Delta.h"
#include "LABounds.h"
#include "Vec.h"
#include "LARefs.h"
#include "LAVar.h"

struct Limits
{
    int model_lim;
    int bound_lim;
    int dec_lim;
};


//
// Class for maintaining the model of a variable
//
class LRAModel
{
private:
    struct ModelEl { Delta d; int dl; };
    struct BoundEl { LABoundRef br; int dl; };
    struct DecEl   { PtAsgn asgn; int dl; };
    vec<vec<ModelEl> > int_model; // The internal model
    vec<vec<BoundEl> > int_lbounds;
    vec<vec<BoundEl> > int_ubounds;
    vec<DecEl>         int_decisions;

    vec<Limits> limits;
    vec<LVRef> model_trace;
    vec<LABoundRef> bound_trace;
    vec<PtAsgn> decision_trace;

    LAVarAllocator &lva;
    LABoundStore &bs;
    int n_vars_with_model;
    LALogic& logic; // Needed just for debug prints
    Map<LVRef,bool,LVRefHash> has_model;
    int backtrackLevel();// { return limits.size() - 1; }
    void         popModels();
    void         popBounds();
    PtAsgn       popDecisions();

public:
    LRAModel(LAVarAllocator &lva, LABoundStore& bs, LALogic& logic) : lva(lva), bs(bs), n_vars_with_model(0), logic(logic) { limits.push({0, 0}); }
    void initModel(LAVarStore &s);
    int addVar(LVRef v); // Adds a variable.  Returns the total number of variables
    inline int   nVars();// { return n_vars_with_model; }
//    void         write(const LVRef &v, const Delta&);
    void         write(const LVRef &v, Delta);
    inline const Delta& read (const LVRef &v) const { assert(hasModel(v)); return int_model[lva[v].ID()].last().d; }
    const  bool  hasModel(const LVRef& v) const;// { return (lva[v].ID() < int_model.size() && int_model[lva[v].ID()].size() > 0); }
//    inline void  pop(const LVRef &v) { int_model[lva[v].ID()].pop(); }

    void pushBound(const LABoundRef br);
    void pushDecision(PtAsgn asgn);
    const LABound& readLBound(const LVRef &v) const;// { return bs[int_lbounds[lva[v].ID()].last().br]; }
    const LABound& readUBound(const LVRef &v) const;// { return bs[int_ubounds[lva[v].ID()].last().br]; }
    const Delta& Lb(LVRef v) const;// { return bs[int_lbounds[lva[v].ID()].last().br].getValue(); }
    const Delta& Ub(LVRef v) const;// { return bs[int_ubounds[lva[v].ID()].last().br].getValue(); }
    void pushBacktrackPoint() ;//     { limits.push({model_trace.size(), bound_trace.size(), decision_trace.size()}); }
    PtAsgn popBacktrackPoint();// { popModels(); popBounds(); PtAsgn popd = popDecisions(); limits.pop(); return popd; }; // Returns the decision if the backtrack point had a decision
    int  getBacktrackSize() const ;//{ return limits.size(); }

    bool isEquality(LVRef v) const;// { return bs[int_lbounds[lva[v].ID()].last().br].getIdx()+1 == bs[int_ubounds[lva[v].ID()].last().br].getIdx() && !Lb(v).isInf() && !Ub(v).isInf() && Lb(v) == Ub(v); }
    bool isUnbounded(LVRef v) const;// { return bs.isUnbounded(v); }
    bool boundSatisfied(LVRef v, LABoundRef b) const;// { return ((bs[b].getType() == bound_u) && !(bs[b].getIdx() < readUBound(v).getIdx())) || ((bs[b].getType() == bound_l) && !(bs[b].getIdx() > readLBound(v).getIdx())); }
    bool boundUnsatisfied(LVRef v, LABoundRef b) const;
   /* { return ((bs[b].getType() == bound_l) && (bs[b].getIdx() > readUBound(v).getIdx() && bs[b].getValue() != Ub(v))) ||
             ((bs[b].getType() == bound_u) && (bs[b].getIdx() < readLBound(v).getIdx() && bs[b].getValue() != Lb(v))); }*/

    void printModelState();

    void clear();
};

#endif //OPENSMT_LRAMODEL_H
