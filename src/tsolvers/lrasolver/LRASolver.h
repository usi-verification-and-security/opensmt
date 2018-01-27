/*********************************************************************
 Author: Leonardo Alt <leonardoaltt@gmail.com>
       , Antti Hyvarinen <antti.hyvarinen@gmail.com>
       , Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
       , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT2 -- Copyright (C) 2012 - 2016, Antti Hyvarinen
                           2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef LRASOLVER_H
#define LRASOLVER_H

//#define GAUSSIAN_DEBUG

#include "Timer.h"
#include "TSolver.h"
#include "LRAModel.h"
#include "LRALogic.h"

#include <unordered_set>
#include <unordered_map>

class LAVar;
class LAVarStore;
class Delta;

class LRASolverStats: public TSolverStats
{
    public:
        int num_pivot_ops;
        int num_bland_ops;
        int num_vars;
        opensmt::OSMTTimeVal simplex_timer;

        LRASolverStats()
        : num_pivot_ops(0)
        , num_bland_ops(0)
        , num_vars(0)
        , TSolverStats()
        {}

        void printStatistics(ostream& os)
        {
            os << "; -------------------------" << endl;
            os << "; STATISTICS FOR LRA SOLVER" << endl;
            os << "; -------------------------" << endl;
            TSolverStats::printStatistics(os);
            os << "; Number of LRA vars.......: " << num_vars << endl;
            os << "; Pivot operations.........: " << num_pivot_ops << endl;
            os << "; Bland operations.........: " << num_bland_ops << endl;
            os << "; Simplex time.............: " << simplex_timer.getTime() << " s\n";
        }
};


//
// Class to solve Linear Arithmetic theories
//

class LRASolver: public TSolver
{
private:

    struct LVRefPair { LVRef p1; LVRef p2; };
//    vector<opensmt::Real*> numbers_pool;    // Collect numbers.  Should work as a simple memory managemet system
    LRALogic&            logic;
    LAVarAllocator       lva;
    LAVarStore           lavarStore;

//    BindedRowsAllocator  bra;
//    BindedRowsStore      bindedRowsStore;
//
//    PolyTermAllocator    pta;
//    PolyAllocator        pa;
//    PolyStore            polyStore;


    LABoundAllocator     ba;
    LABoundListAllocator bla;
    LABoundStore         boundStore;


    // Possible internal states of the solver
    typedef enum
    {
        INIT, INCREMENT, SAT, UNSAT, ERROR
    } LRASolverStatus;

    opensmt::Real delta; // The size of one delta.  Set through computeModel()
    unsigned bland_threshold;
    LRASolverStats tsolver_stats;
    void initSlackVar(LVRef s);
    void setBound(PTRef leq);

//    opensmt::Real *newReal(const Real *old);

    int debug_check_count;
    int debug_assert_count;
    int debug_pivot_sum_count;

public:

    LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d);

    ~LRASolver( );                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    lbool declareTerm        (PTRef tr) override;                // Inform the theory solver about the existence of a literal
    bool  check              ( bool ) override;                  // Checks the satisfiability of current constraints
    bool  assertLit          ( PtAsgn , bool = false ) override; // Push the constraint into Solver
    void  pushBacktrackPoint ( ) override;                       // Push a backtrack point
    void  popBacktrackPoint  ( ) override;                       // Backtrack to last saved point
    void  popBacktrackPoints  ( unsigned int ) override;         // Backtrack given number of saved points
    void  fixStackConsistency( );                                // Adjust the models so that non-basic (column) variables do not break asserted bounds
    void  fixCandidates( );                                      // Reset row candidates for possible out of bounds


    // Return the conflicting bounds
    void  getConflict(bool, vec<PtAsgn>& e) override;
    PtAsgn_reason getDeduction() override { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

    LRALogic&  getLogic() override { return logic; }
    bool       isValid(PTRef tr) override;
    const void getRemoved(vec<PTRef>&) const;  // Fill the vector with the vars removed due to not having bounds

#ifdef PRODUCE_PROOF
    TheoryInterpolator* getTheoryInterpolator() override { return nullptr; }
    PTRef getInterpolant( const ipartitions_t &, map<PTRef, icolor_t>* );
    PTRef getExperimentalInterpolant( const ipartitions_t & mask , map<PTRef, icolor_t> *labels);
    bool usingStrong() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_strong; }
    bool usingWeak() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_weak; }
    bool usingFactor() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_factor; }
    bool usingExperimental() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_experimental; }
    const char*  getStrengthFactor() { return config.getLRAStrengthFactor(); }
#endif

protected:
    // vector in which witnesses for unsatisfiability are stored
    vector<opensmt::Real> explanationCoefficients;

    vec<LVRef> columns;                 // The columns
    vec<LVRef> rows;                    // The rows
    std::unordered_map<LVRef, std::unordered_map<LVRef, Real,LVRefHash>, LVRefHash> row_polynomials;
    std::unordered_map<LVRef, std::unordered_set<LVRef, LVRefHash>, LVRefHash> col_occ_list;
    template<class T> inline T max(T a, T b) const { return a > b ? a : b; }
    bool assertBoundOnVar(LVRef it, LABoundRef it_i);

    vector<unsigned> checks_history;

    unsigned nVars() const { return lva.getNumVars(); }

private:
//    void getReal(opensmt::Real*&, const PTRef);              // Get a new real possibly using the number pool
    opensmt::Real getReal(PTRef);
    LVRef constructLAVarSystem(PTRef term);                 // Find a LAVar for term and all LA vars appearing in term.  Return the LAVar for the term.  iu
    LVRef getLAVar_single(PTRef term);                      // Initialize a new LA var if needed, otherwise return the old var
    bool hasVar(PTRef expr);
    void setNonbasic(LVRef);
    void setBasic(LVRef);
//    void doGaussianElimination( );                          // Performs Gaussian elimination of all redundant terms in the Tableau
//    void removeRow(PolyRef pr);                                // Remove the row corresponding to v
//    void removeCol(LVRef v);                                // Remove the col corresponding to v
    void update( LVRef, const Delta & );                    // Updates the bounds after constraint pushing
    void pivotAndUpdate( LVRef, LVRef, const Delta &);      // Updates the tableau after constraint pushing
    void getConflictingBounds( LVRef, vec<PTRef> & );       // Returns the bounds conflicting with the actual model
    void getDeducedBounds( const Delta& c, BoundT, vec<PtAsgn_reason>& dst, SolverId solver_id ); // find possible deductions by value c
    void getDeducedBounds( BoundT, vec<PtAsgn_reason>& dst, SolverId solver_id );                 // find possible deductions for actual bounds values
    void getSuggestions( vec<PTRef>& dst, SolverId solver_id );                                   // find possible suggested atoms
    void getSimpleDeductions(LVRef v, LABoundRef);      // find deductions from actual bounds position
    unsigned getIteratorByPTRef( PTRef e, bool );                                                 // find bound iterator by the PTRef
    void refineBounds( );                                   // Compute the bounds for touched polynomials and deduces new bounds from it
    inline bool getStatus( );                               // Read the status of the solver in lbool
    inline bool setStatus( LRASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver
    void print( ostream & out ) override;                            // Prints terms, current bounds and the tableau
//    void addVarToRow( LVRef, LVRef, opensmt::Real*);
    bool checkIntegersAndSplit();                           //

    // Value system + history of bounds
    LRAModel model;

    // Out of bound candidates
    std::unordered_set<LVRef, LVRefHash> candidates;

    // Model & bounds
    bool isEquality(LVRef) const;
    const Delta overBound(LVRef) const;
    bool isModelOutOfBounds  (LVRef v) const;
    bool isModelOutOfUpperBound(LVRef v) const;
    bool isModelOutOfLowerBound(LVRef v) const;
    bool isModelInteger (LVRef v) const;
    void computeConcreteModel(LVRef v);
    Delta evalSum(PTRef tr) const;
    vec<opensmt::Real*> concrete_model;              // Save here the concrete model for the vars indexed by Id
    const Delta overBound(LVRef v);
    void computeModel() override;                             // The implementation for the interface
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

    bool first_update_after_backtrack;

    LRASolverStatus status;                  // Internal status of the solver (different from bool)

    // The variable system
    class ModelPoly {
        vec<PolyTermRef> poly;
    public:
        ModelPoly() {}
        ModelPoly(const ModelPoly &o) { o.poly.copyTo(poly); }
        ModelPoly(const vec<PolyTermRef>& v) { v.copyTo(poly); }
        PolyTermRef operator[](int i) const { return poly[i]; }
        void operator=(const ModelPoly &o) { o.poly.copyTo(poly); }
        int size() const { return poly.size(); }
    };
    Map<PTRef,ModelPoly,PTRefHash> removed_by_GaussianElimination;       // Stack of variables removed during Gaussian elimination
//    void solveForVar(PolyRef pr, int idx, vec<PolyTermRef>& expr);       // Solve the poly pr for the variable pr[idx] and place the resulting expression to expr

    // Two reloaded output operators
    inline friend ostream & operator <<( ostream & out, LRASolver & solver )
    {
        solver.print( out );
        return out;
    }

    inline friend ostream & operator <<( ostream & out, LRASolver * solver )
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
    bool valueConsistent(LVRef v); // Debug: Checks that the value of v in the model is consistent with the evaluated value of the polynomial of v in the same model.
    bool stackOk();
    bool checkConsistency();
    bool checkTableauConsistency();
    bool checkRowConsistency();
    bool checkColumnConsistency();
    void crashInconsistency(LVRef v, int line);
};

#endif
