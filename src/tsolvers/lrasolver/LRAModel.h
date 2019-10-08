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
#include "LAVarMapper.h"

struct Limits
{
    int model_lim;
    int bound_lim;
};


//
// Class for maintaining the model of a variable
//
class LRAModel
{
protected:
    struct ModelEl { Delta d; int dl; };
    struct BoundEl { LABoundRef br; int dl; };
    vec<vec<ModelEl> > int_model; // The internal model
    vec<vec<BoundEl> > int_lbounds;
    vec<vec<BoundEl> > int_ubounds;

    vec<Limits> limits;
    vec<LVRef> model_trace;
    vec<LABoundRef> bound_trace;

    LABoundStore &bs;
    int n_vars_with_model;
    Map<LVRef,bool,LVRefHash> has_model;
    int          backtrackLevel();
    void         popModels();
    void         popBounds();

public:
    LRAModel(LABoundStore & bs) : bs(bs), n_vars_with_model(0) { limits.push({0, 0}); }
    void init();
    int addVar(LVRef v); // Adds a variable.  Returns the total number of variables
    inline int   nVars() { return n_vars_with_model; }

    void         write(const LVRef &v, Delta);
    inline const Delta& read (const LVRef &v) const { assert(hasModel(v)); return int_model[getVarId(v)].last().d; }
    const  bool  hasModel(const LVRef& v) const;

    void pushBound(const LABoundRef br);
    const LABound& readLBound(const LVRef &v) const;
    LABoundRef readLBoundRef(LVRef v) const;
    const LABound& readUBound(const LVRef &v) const;
    LABoundRef readUBoundRef(LVRef v) const;
    const Delta& Lb(LVRef v) const;
    const Delta& Ub(LVRef v) const;
    virtual void pushBacktrackPoint();
    virtual void popBacktrackPoint();
    int  getBacktrackSize() const ;

    bool isEquality(LVRef v) const;
    bool isUnbounded(LVRef v) const;
    bool boundSatisfied(LVRef v, LABoundRef b) const;
    bool boundUnsatisfied(LVRef v, LABoundRef b) const;

    void printState() const;

    virtual void clear();
};

#endif //OPENSMT_LRAMODEL_H
