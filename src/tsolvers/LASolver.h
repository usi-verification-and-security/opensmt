#ifndef LASOLVER_H
#define LASOLVER_H

//#define GAUSSIAN_DEBUG

#include "Timer.h"
#include "LALogic.h"

#include "TSolver.h"
#include "lrasolver/LRAModel.h"
#include "lrasolver/Tableau.h"
#include "lrasolver/Polynomial.h"

#include <unordered_set>
#include <unordered_map>

class LAVar;
class LAVarStore;
class Delta;

class LASolverStats: public TSolverStats
{
    public:
        int num_pivot_ops;
        int num_bland_ops;
        int num_vars;
        opensmt::OSMTTimeVal timer;

        LASolverStats()
        : num_pivot_ops(0)
        , num_bland_ops(0)
        , num_vars(0)
        , TSolverStats()
        {}

        void printStatistics(ostream& os)
        {
            os << "; -------------------------" << endl;
            os << "; STATISTICS FOR LA SOLVER" << endl;
            os << "; -------------------------" << endl;
            TSolverStats::printStatistics(os);
            os << "; Number of LA vars.......: " << num_vars << endl;
            os << "; Pivot operations.........: " << num_pivot_ops << endl;
            os << "; Bland operations.........: " << num_bland_ops << endl;
            os << "; LA time.............: " << timer.getTime() << " s\n";
        }
};


//
// Class to solve Linear Arithmetic theories
//

class LASolver: public TSolver
{

protected:

    LALogic&            logic;
    LAVarAllocator       lva;
    LAVarStore           lavarStore;

    LABoundAllocator     ba;
    LABoundListAllocator bla;
    LABoundStore         boundStore;


    // Possible internal states of the solver
    typedef enum
    {
        INIT, INCREMENT, SAT, UNSAT, ERROR
    } LASolverStatus;

    //opensmt::Real delta; // The size of one delta.  Set through computeModel()
    unsigned bland_threshold;
    LASolverStats tsolver_stats;
    void setBound(PTRef leq);

public:

    LASolver(SolverDescr dls, SMTConfig & c, LALogic& l, vec<DedElem>& d);

    ~LASolver( );                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    lbool declareTerm        (PTRef tr) override;                // Inform the theory solver about the existence of a literal
    bool  check              ( bool ) override;                  // Checks the satisfiability of current constraints
    bool  check_simplex  (bool);
    bool  assertLit          ( PtAsgn , bool = false ) override; // Push the constraint into Solver
    void  pushBacktrackPoint ( ) override;                       // Push a backtrack point
    void  popBacktrackPoint  ( ) override;                       // Backtrack to last saved point
    void  popBacktrackPoints  ( unsigned int ) override;         // Backtrack given number of saved points


    // Return the conflicting bounds
    void  getConflict(bool, vec<PtAsgn>& e) override;
    PtAsgn_reason getDeduction() override { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

    LALogic&  getLogic() override { return logic; }
    bool       isValid(PTRef tr) override;

#ifdef PRODUCE_PROOF
    TheoryInterpolator* getTheoryInterpolator() override { return nullptr; }
    PTRef getInterpolant( const ipartitions_t &, map<PTRef, icolor_t>* );
    bool usingStrong() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_strong; }
    bool usingWeak() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_weak; }
    bool usingFactor() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_factor; }
    const char*  getStrengthFactor() { return config.getLRAStrengthFactor(); }
#endif

protected:
    Tableau tableau;

    LVRef exprToLVar(PTRef expr); // Ensures this term and all variables in it has corresponding LVAR.  Returns the LAVar for the term.
    void pivot(LVRef basic, LVRef nonBasic);


    virtual Polynomial expressionToLVarPoly(PTRef expression);
    LVRef getBasicVarToFixByBland() const;
    LVRef getBasicVarToFixByShortestPoly() const;
    LVRef findNonBasicForPivotByBland(LVRef basicVar);
    LVRef findNonBasicForPivotByHeuristic(LVRef basicVar);
    void updateValues(LVRef basicVar, LVRef nonBasicVar);


//protected:
    // vector in which witnesses for unsatisfiability are stored
    vector<opensmt::Real> explanationCoefficients;

    bool assertBoundOnVar(LVRef it, LABoundRef it_i);

    unsigned nVars() const { return lva.getNumVars(); }
    void  fixCandidates( );                                      // Reset row candidates for possible out of bounds

//private:
//    void getReal(opensmt::Real*&, const PTRef);              // Get a new real possibly using the number pool
    opensmt::Number getNum(PTRef);

    LVRef getLAVar_single(PTRef term);                      // Initialize a new LA var if needed, otherwise return the old var
    bool hasVar(PTRef expr);
    void doGaussianElimination( );                          // Performs Gaussian elimination of all redundant terms in the Tableau
//    void removeRow(PolyRef pr);                                // Remove the row corresponding to v
//    void removeCol(LVRef v);                                // Remove the col corresponding to v
    void changeValueBy( LVRef, const Delta & );                    // Updates the bounds after constraint pushing
    //void pivotAndUpdate( LVRef, LVRef, const Delta &);      // Updates the tableau after constraint pushing
    void getConflictingBounds( LVRef, vec<PTRef> & );       // Returns the bounds conflicting with the actual model
    void getDeducedBounds( const Delta& c, BoundT, vec<PtAsgn_reason>& dst, SolverId solver_id ); // find possible deductions by value c
    void getDeducedBounds( BoundT, vec<PtAsgn_reason>& dst, SolverId solver_id );                 // find possible deductions for actual bounds values
    void getSuggestions( vec<PTRef>& dst, SolverId solver_id );                                   // find possible suggested atoms
    void getSimpleDeductions(LVRef v, LABoundRef);      // find deductions from actual bounds position
    unsigned getIteratorByPTRef( PTRef e, bool );                                                 // find bound iterator by the PTRef
    void refineBounds( );                                   // Compute the bounds for touched polynomials and deduces new bounds from it
    inline bool getStatus( );                               // Read the status of the solver in lbool
    inline bool setStatus( LASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver
    void print( ostream & out ) override;                            // Prints terms, current bounds and the tableau
//    void addVarToRow( LVRef, LVRef, opensmt::Real*);
    //bool checkIntegersAndSplit();                           //PS. needs to be defined in LIASOLVER.H
    bool isProcessedByTableau(LVRef var) {return tableau.isProcessed(var);}

    // Value system + history of bounds
    LRAModel model;

    // Out of bound candidates
    mutable std::unordered_set<LVRef, LVRefHash> candidates;

    // Model & bounds
    bool isEquality(LVRef) const;
    const Delta overBound(LVRef) const;
    bool isModelOutOfBounds  (LVRef v) const;
    bool isModelOutOfUpperBound(LVRef v) const;
    bool isModelOutOfLowerBound(LVRef v) const;
    //bool isModelInteger (LVRef v) const;
    virtual void computeConcreteModel(LVRef v);
    Delta evalSum(PTRef tr) const;
    vec<opensmt::Real*> concrete_model;              // Save here the concrete model for the vars indexed by Id
    const Delta overBound(LVRef v);
    virtual void computeModel() override;                             // The implementation for the interface
    opensmt::Real evaluateTerm(PTRef tr);
    // Binded Rows system
//    inline BindedRows& getBindedRows(LVRef v) { return bra[lva[v].getBindedRowsRef()]; }
//    void unbindRow(LVRef v, int row);


    // Polynomials system
//    void  makePoly      (LVRef s, PTRef pol);     // Create a polynomial, introducing new LAVars if necessary
//    Poly& getPoly       (LVRef s) { return pa[lva[s].getPolyRef()]; }

    // Bounds system
    vec<LABoundRefPair> ptermToLABoundRefs;
    const LABoundRef getBound(LVRef v, int idx) const { return boundStore.getBoundByIdx(v, idx); }
    bool isUnbounded (LVRef v) const;

    LASolverStatus status;                  // Internal status of the solver (different from bool)

    std::unordered_map<LVRef,Polynomial, LVRefHash> removed_by_GaussianElimination;       // Stack of variables removed during Gaussian elimination
//    void solveForVar(PolyRef pr, int idx, vec<PolyTermRef>& expr);       // Solve the poly pr for the variable pr[idx] and place the resulting expression to expr

    // Two reloaded output operators
    inline friend ostream & operator <<( ostream & out, LASolver & solver )
    {
        solver.print( out );
        return out;
    }

    inline friend ostream & operator <<( ostream & out, LASolver * solver )
    {
        solver->print( out );
        return out;
    }
    ValPair getValue(PTRef tr) override;  // Computes the model and changes state.
    inline int     verbose                       ( ) const { return config.verbosity(); }

    // Debug stuff
    char* printValue(PTRef tr) override { char* tmp = (char*)malloc(1); tmp[0] = '\0'; return tmp; } // Implement later...
    char* printExplanation(PTRef tr) override { return printValue(tr); } // Implement later...
    void isProperLeq(PTRef tr);  // The Leq term conforms to the assumptions of its form.  Only asserts.
    char* printVar(LVRef v);
    bool valueConsistent(LVRef v) const; // Debug: Checks that the value of v in the model is consistent with the evaluated value of the polynomial of v in the same model.
    bool checkValueConsistency() const;
    bool invariantHolds() const;
    bool checkTableauConsistency() const;
    void crashInconsistency(LVRef v, int line);
};

#endif
