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
    std::unique_ptr<LRAModel> model;
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
    struct ExplTerm {
        LABoundRef boundref;
        opensmt::Real coeff;
    };
    using Explanation = std::vector<ExplTerm>;

    Simplex(SMTConfig& c, std::unique_ptr<LRAModel> model, LABoundStore &bs) : model(std::move(model)), c(c), bland_threshold(1000), boundStore(bs) {}
    Simplex(SMTConfig& c, LABoundStore&bs) : model(new LRAModel(bs)), c(c), bland_threshold(1000), boundStore(bs) {}
    ~Simplex();

    void initModel() { model->init(); }

    void doGaussianElimination();                           // Performs Gaussian elimination of all redundant terms in the Tableau if applicable
    void clear() { model->clear(); candidates.clear(); tableau.clear(); removed_by_GaussianElimination.clear();}
    Explanation checkSimplex();
    void pushBacktrackPoint() { model->pushBacktrackPoint(); }
    void popBacktrackPoint()  { model->popBacktrackPoint(); }
    Explanation assertBoundOnVar(LVRef it, LABoundRef itBound_ref);
    bool isProcessedByTableau  (LVRef var) const;
    bool isModelOutOfBounds    (LVRef v) const;
    bool isModelOutOfUpperBound(LVRef v) const;
    bool isModelOutOfLowerBound(LVRef v) const;
    void newNonbasicVar(LVRef v) { tableau.newNonbasicVar(v); }
    void nonbasicVar(LVRef v)    { tableau.nonbasicVar(v); }
    void newBasicVar(LVRef x, std::unique_ptr<Polynomial> poly) { tableau.newBasicVar(x, std::move(poly)); }
    Explanation getConflictingBounds(LVRef x);
    bool checkValueConsistency() const;
    bool invariantHolds() const;
    bool isRemovedByGaussianElimination(LVRef v) const { return removed_by_GaussianElimination.find(v) != removed_by_GaussianElimination.end(); }
    std::unordered_map<LVRef,Polynomial,LVRefHash>::const_iterator getRemovedByGaussianElimination(LVRef v) const { return removed_by_GaussianElimination.find(v); }

    opensmt::Real computeDelta() const;
    bool hasModel(LVRef v) const { return model->hasModel(v); }
    Delta getValuation(LVRef) const;                     // Understands also variables deleted by gaussian elimination
    Delta read(LVRef v) const { return model->read(v); } // ignores unsafely variables deleted by gaussian elimination
    const LABoundRef readLBoundRef(const LVRef &v) const { return model->readLBoundRef(v); }
    const LABoundRef readUBoundRef(const LVRef &v) const { return model->readUBoundRef(v); }
    const Delta& Lb(LVRef v) const { return model->Lb(v); }
    const Delta& Ub(LVRef v) const { return model->Ub(v); }

    void printModelState() const { model->printState(); };
};


#endif //OPENSMT_SIMPLEX_H