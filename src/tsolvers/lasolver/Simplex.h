//
// Created by prova on 06.09.19.
//

#ifndef OPENSMT_SIMPLEX_H
#define OPENSMT_SIMPLEX_H

#include "lrasolver/LABounds.h"
#include "lrasolver/Tableau.h"
#include "lrasolver/LAVar.h"
#include "lrasolver/LRAModel.h"
#include "SMTConfig.h"

class SimplexStats {
public:
    int num_bland_ops;
    int num_pivot_ops;
    SimplexStats() : num_bland_ops(0), num_pivot_ops(0) {}
};

class Simplex {
    LABoundStore& boundStore;
    unsigned bland_threshold;
    Tableau tableau;
    SimplexStats simplex_stats;
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
    LRAModel &model;
    // Out of bound candidates
    // mutable std::unordered_set<LVRef, LVRefHash> candidates;
    mutable std::set<LVRef, LVRefComp> candidates;
    bool isEquality(LVRef) const;
    const Delta overBound(LVRef) const;
    // Model & bounds

    const LABoundRef getBound(LVRef v, int idx) const ;//{ return boundStore.getBoundByIdx(v, idx); }
    bool isUnbounded (LVRef v) const;
    std::unordered_map<LVRef,Polynomial, LVRefHash> removed_by_GaussianElimination;       // Stack of variables removed during Gaussian elimination
    bool valueConsistent(LVRef v) const; // Debug: Checks that the value of v in the model is consistent with the evaluated value of the polynomial of v in the same model.
    bool checkTableauConsistency() const;
    SMTConfig& c;
public:
    Simplex(SMTConfig& c, LRAModel& model, LABoundStore &bs) : model(model), c(c), bland_threshold(1000), boundStore(bs) {}
    void doGaussianElimination();                           // Performs Gaussian elimination of all redundant terms in the Tableau if applicable
    void clear() { candidates.clear(); tableau.clear(); removed_by_GaussianElimination.clear();}
    bool checkSimplex(std::vector<LABoundRef> &explanation, std::vector<opensmt::Real> &explanationCoefficients);
    bool assertBoundOnVar(LVRef it, LABoundRef itBound_ref, std::vector<LABoundRef> &explanation, std::vector<opensmt::Real> &explanationCoefficients);
    bool isProcessedByTableau  (LVRef var) const;
    bool isModelOutOfBounds    (LVRef v) const;
    bool isModelOutOfUpperBound(LVRef v) const;
    bool isModelOutOfLowerBound(LVRef v) const;
    std::unique_ptr<Polynomial> addPoly(std::unique_ptr<std::vector<std::pair<LVRef,opensmt::Real>>> terms);
    void newNonbasicVar(LVRef v) { tableau.newNonbasicVar(v); }
    void newBasicVar(LVRef x, std::unique_ptr<Polynomial> poly) { tableau.newBasicVar(x, std::move(poly)); }
    void getConflictingBounds(LVRef x, std::vector<LABoundRef> &explanation, std::vector<opensmt::Real> &explanationCoefficients);
    bool checkValueConsistency() const;
    bool invariantHolds() const;
    bool isRemovedByGaussianElimination(LVRef v) const { return removed_by_GaussianElimination.find(v) != removed_by_GaussianElimination.end(); }
    std::unordered_map<LVRef,Polynomial,LVRefHash>::const_iterator getRemovedByGaussianElimination(LVRef v) const { return removed_by_GaussianElimination.find(v); }

};


#endif //OPENSMT_SIMPLEX_H