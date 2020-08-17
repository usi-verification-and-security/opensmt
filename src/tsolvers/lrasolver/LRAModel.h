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
#include "NatSet.h"

//
// Class for maintaining the model of a variable
//
class LRAModel
{
protected:
    vec<vec<LABoundRef> > int_lbounds;
    vec<vec<LABoundRef> > int_ubounds;

    vec<Delta>  current_assignment;
    vec<Delta>  last_consistent_assignment;
    nat_set     changed_vars_set;
    vec<LVRef>  changed_vars_vec;

    LABoundStore &bs;
    int n_vars_with_model;
    Map<LVRef,bool,LVRefHash> has_model;
    void         popBounds();

public:
    LRAModel(LABoundStore & bs) : bs(bs), n_vars_with_model(0) { }
    void init();
    int addVar(LVRef v); // Adds a variable.  Returns the total number of variables
    inline int   nVars() { return n_vars_with_model; }

    void         write(const LVRef &v, Delta);
    inline const Delta& read (const LVRef &v) const { return current_assignment[getVarId(v)]; }
private:
    // needed from Simplex to make all work properly with backtracking and quasi-basic variables
    friend class Simplex;
    void         restoreVarWithValue(LVRef v, Delta val) {
        current_assignment[getVarId(v)] = val;
        last_consistent_assignment[getVarId(v)] = std::move(val);
    }
    inline const Delta& readBackupValue (LVRef v) const { return last_consistent_assignment[getVarId(v)]; }
public:

    bool hasActiveBounds(LVRef v) const { return hasLBound(v) || hasUBound(v); }
    void pushBound(const LABoundRef br);
    void popBound(LVRef var, BoundT type);
    bool hasLBound(LVRef v) const { return int_lbounds[getVarId(v)].size() != 0; }
    const LABound& readLBound(const LVRef &v) const;
    LABoundRef readLBoundRef(LVRef v) const;
    bool hasUBound(LVRef v) const { return int_ubounds[getVarId(v)].size() != 0; }
    const LABound& readUBound(const LVRef &v) const;
    LABoundRef readUBoundRef(LVRef v) const;
    inline const Delta& Lb(LVRef v) const { return readLBound(v).getValue(); }
    inline const Delta& Ub(LVRef v) const { return readUBound(v).getValue(); }

    bool isEquality(LVRef v) const;
    bool isUnbounded(LVRef v) const;
    bool boundTriviallySatisfied(LABoundRef b) const;
    bool boundTriviallyUnsatisfied(LABoundRef b) const;

    void saveAssignment() {
        for (int i = 0; i < changed_vars_vec.size(); ++i) {
            LVRef v = changed_vars_vec[i];
            last_consistent_assignment[getVarId(v)] = current_assignment[getVarId(v)];
        }
        changed_vars_vec.clear();
        changed_vars_set.reset();
    }

    void restoreAssignment() {
        for (int i = 0; i < changed_vars_vec.size(); ++i) {
            LVRef v = changed_vars_vec[i];
            current_assignment[getVarId(v)] = last_consistent_assignment[getVarId(v)];
        }
        changed_vars_vec.clear();
        changed_vars_set.reset();
    }

    void clear();
};

#endif //OPENSMT_LRAMODEL_H
