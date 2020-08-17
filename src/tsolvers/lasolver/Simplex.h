//
// Created by prova on 06.09.19.
//

#ifndef OPENSMT_SIMPLEX_H
#define OPENSMT_SIMPLEX_H

#include "lasolver/LABounds.h"
#include "lasolver/Tableau.h"
#include "lasolver/LAVar.h"
#include "lrasolver/LRAModel.h"
#include "SMTConfig.h"

class SimplexStats {
public:
    int num_bland_ops;
    int num_pivot_ops;
    SimplexStats() : num_bland_ops(0), num_pivot_ops(0) {}
    void printStatistics(ostream& os)
    {
        os << "; -------------------------" << endl;
        os << "; STATISTICS FOR SIMPLEX   " << endl;
        os << "; -------------------------" << endl;
        os << "; Pivot operations.........: " << num_pivot_ops << endl;
        os << "; Bland operations.........: " << num_bland_ops << endl;
    }
};

class Simplex {
    std::unique_ptr<LRAModel> model;
    LABoundStore& boundStore;

    Tableau tableau;
    SimplexStats simplex_stats;

    // Now simplex is in charge of backtrack points
    vec<int> bound_limits;
    vec<LABoundRef> bound_trace;

    void  pivot(LVRef basic, LVRef nonBasic);
    LVRef getBasicVarToFixByBland() const;
    LVRef getBasicVarToFixByShortestPoly() const;
    LVRef findNonBasicForPivotByBland(LVRef basicVar);
    LVRef findNonBasicForPivotByHeuristic(LVRef basicVar);
    void  updateValues(LVRef basicVar, LVRef nonBasicVar);
    inline void newCandidate(LVRef candidateVar);
    inline void eraseCandidate(LVRef candidateVar);

    void changeValueBy( LVRef, const Delta & );             // Updates the bounds after constraint pushing
    void refineBounds() { return; }                         // Compute the bounds for touched polynomials and deduces new bounds from it
    // Out of bound candidates
    // mutable std::unordered_set<LVRef, LVRefHash> candidates;
    mutable std::set<LVRef, LVRefComp> candidates;
//    bool isEquality(LVRef) const;
    const Delta overBound(LVRef) const;
    // Model & bounds

    const LABoundRef getBound(LVRef v, int idx) const ;//{ return boundStore.getBoundByIdx(v, idx); }
    bool isUnbounded (LVRef v) const;

    bool valueConsistent(LVRef v) const; // Debug: Checks that the value of v in the model is consistent with the evaluated value of the polynomial of v in the same model.
    bool checkTableauConsistency() const;
public:
    struct ExplTerm {
        LABoundRef boundref;
        opensmt::Real coeff;
    };
    using Explanation = std::vector<ExplTerm>;

    Simplex(LABoundStore&bs) : model(new LRAModel(bs)), boundStore(bs) { bound_limits.push(0); }
    ~Simplex();

    void initModel() { model->init(); }

    void clear();
    Explanation checkSimplex();
    void pushBacktrackPoint() { bound_limits.push(bound_trace.size()); }
    void popBacktrackPoint()  { popBounds(); bound_limits.pop(); }
    inline void finalizeBacktracking() {
        assert(model->changed_vars_vec.size() == 0);
        candidates.clear();
        bufferOfActivatedBounds.clear();
        assert(checkValueConsistency());
        assert(invariantHolds());
    }

    void quasiToBasic(LVRef it);

    Simplex::Explanation assertBound(LABoundRef bound_ref);
    bool isProcessedByTableau  (LVRef var) const;
    inline bool isModelOutOfBounds    (LVRef v) const { return isModelOutOfUpperBound(v) || isModelOutOfLowerBound(v); }
    inline bool isModelOutOfUpperBound(LVRef v) const { return ( model->hasUBound(v) && model->read(v) > model->Ub(v) ); }
    inline bool isModelOutOfLowerBound(LVRef v) const { return ( model->hasLBound(v) && model->read(v) < model->Lb(v) ); }

    // No upper bound count as +infinity
    inline bool isModelStrictlyUnderUpperBound(LVRef v) const { return ( !model->hasUBound(v) || model->read(v) < model->Ub(v) ); }
    // No lower bound count as -infinity
    inline bool isModelStrictlyOverLowerBound(LVRef v) const { return ( !model->hasLBound(v) || model->read(v) > model->Lb(v) ); }

    void newNonbasicVar(LVRef v) { newVar(v); tableau.newNonbasicVar(v); }
    void nonbasicVar(LVRef v)    { newVar(v); tableau.nonbasicVar(v); }
    void newRow(LVRef x, std::unique_ptr<Polynomial> poly) { newVar(x); tableau.newRow(x, std::move(poly)); }
    Explanation getConflictingBounds(LVRef x, bool conflictOnLower);
    bool checkValueConsistency() const;
    bool invariantHolds() const;

    opensmt::Real computeDelta() const;
    Delta getValuation(LVRef) const;                     // Understands also variables deleted by gaussian elimination
//    Delta read(LVRef v) const { assert(!tableau.isQuasiBasic(v)); return model->read(v); } // ignores unsafely variables deleted by gaussian elimination
    const LABoundRef readLBoundRef(const LVRef &v) const { return model->readLBoundRef(v); }
    const LABoundRef readUBoundRef(const LVRef &v) const { return model->readUBoundRef(v); }
    const Delta& Lb(LVRef v) const { return model->Lb(v); }
    const Delta& Ub(LVRef v) const { return model->Ub(v); }
    bool hasLBound(LVRef v) const {return model->hasLBound(v); }
    bool hasUBound(LVRef v) const {return model->hasUBound(v); }

    // Keeping track of activated bounds
private:
    vec<LABoundRef> bufferOfActivatedBounds;

    void newVar(LVRef v) {
        // MB: is this needed for something?
    }

    void processBufferOfActivatedBounds();

    void activateBound(LABoundRef boundRef) {
        LVRef var = boundStore[boundRef].getLVRef();
        assert(not tableau.isQuasiBasic(var) || not model->hasActiveBounds(var));
        model->pushBound(boundRef);
        bound_trace.push(boundRef);
        if (tableau.isQuasiBasic(var)) {
            quasiToBasic(var);
        }
    }

    void popBounds();

public:

    lbool chooseBoundPolarity(LABoundRef pos, LABoundRef neg) const {
        LVRef var = boundStore[pos].getLVRef();
        assert(var == boundStore[neg].getLVRef());
        if (tableau.isQuasiBasic(var)) {
            (const_cast<Simplex*>(this))->quasiToBasic(var);
        }
        auto const& val = model->read(var);
        bool positive = false;
        auto const& positive_bound = this->boundStore[pos];
        if ((positive_bound.getType() == bound_l && positive_bound.getValue() <= val)
            || (positive_bound.getType() == bound_u && positive_bound.getValue() >= val)) {
            // The current value of the variable is consistent with the positive bound
            positive = true;
        }
        bool negative = false;
        auto const& negative_bound = this->boundStore[neg];
        if ((negative_bound.getType() == bound_l && negative_bound.getValue() <= val)
            || (negative_bound.getType() == bound_u && negative_bound.getValue() >= val)) {
            // The current value of the variable is consistent with the negative bound
            negative = true;
        }
        // The value cannot be consistent with bound positive and negative bound at the same time
        assert(!positive || !negative);
        // It can happen that neither bound is consistent with the current assignment. Consider the current value
        // of variable "x" as <0,-1/2> with term "x >= 0". The positive bound is lower with value <0,0> and the negative
        // bound is upper with value <0, -1>. Then both "positive" and "negative" will be false
        if (positive) { return l_True; }
        if (negative) { return l_False; }
        return l_Undef;
    }
};


#endif //OPENSMT_SIMPLEX_H
