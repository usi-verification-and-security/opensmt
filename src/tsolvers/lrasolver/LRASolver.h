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
#include "LRALogic.h"
#include "TSolver.h"
#include "LAVar.h"
#include "Polynomials.h"
#include "BindedRows.h"
#include "LABounds.h"

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
// Class for maintaining the model of a variable
//
class LRAModel
{
private:
    struct ModelEl { Delta d; int dl; };
    vec<vec<ModelEl> > int_model; // The internal model
    LAVarAllocator &lva;
    int n_vars_with_model;
    Map<LVRef,bool,LVRefHash> has_model;
public:
    LRAModel(LAVarAllocator &lva) : lva(lva) {}
    int addVar(LVRef v); // Adds a variable.  Returns the total number of variables
    inline int   nVars() { return n_vars_with_model; }
    inline       Delta& operator[] (const LVRef &v);
    inline const Delta& operator[] (const LVRef &v) const { return int_model[lva[v].ID()].last().d; }
    inline void  pop(const LVRef &v) { int_model[lva[v].ID()].pop(); }
};

//
// Class to solve Linear Arithmetic theories
//

class LRASolver: public TSolver
{
private:

    vector<Real*>        numbers_pool;    // Collect numbers.  Should work as a simple memory managemet system
    LRALogic&            logic;
    LAVarAllocator       lva;
    LAVarStore           lavarStore;
    PolyAllocator        pa;
    PolyStore            polyStore;
    BindedRowStore       boundedRowStore;
    BindedRowAllocator   bra;
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


public:

    LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d);

    ~LRASolver( );                                      // Destructor ;-)

    virtual void clearSolver(); // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    lbool declareTerm        (PTRef tr);                // Inform the theory solver about the existence of a literal
    bool  check              ( bool );                  // Checks the satisfiability of current constraints
    bool  assertLit          ( PtAsgn , bool = false ); // Push the constraint into Solver
    void  pushBacktrackPoint ( );                       // Push a backtrack point
    void  popBacktrackPoint  ( );                       // Backtrack to last saved point



    void  getConflict(bool, vec<PtAsgn>& e) { for (int i = 0; i < explanation.size(); i++) { e.push(explanation[i]); } } // Return the conflicting bounds
    PtAsgn_reason getDeduction() { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

    LRALogic&  getLogic() { return logic; }
    bool       isValid(PTRef tr);
    const void getRemoved(vec<PTRef>&) const;  // Fill the vector with the vars removed due to not having bounds

    char* printVar(LVRef v) const;
#ifdef PRODUCE_PROOF
    TheoryInterpolator* getTheoryInterpolator() { return NULL; }
    PTRef getInterpolant( const ipartitions_t &, map<PTRef, icolor_t>* );
    bool usingStrong() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_strong; }
    bool usingWeak() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_weak; }
    bool usingFactor() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_factor; }
    const char*  getStrengthFactor() { return config.getLRAStrengthFactor(); }
#endif

protected:
    // vector in which witnesses for unsatisfiability are stored
    vector<Real> explanationCoefficients;

    vec<LVRef> columns;                 // Maps terms' ID to LAVar pointers
    vec<LVRef> rows;                    // Maps terms' ID to LAVar pointers, used to store basic columns
    vec<LVRef> ptermToLavar;            // Maps original constraints to solver's terms and bounds.  Could this be moved to LAVarStore?

    bool assertBoundOnColumn( LVRef it, unsigned it_i);

    vector<unsigned> checks_history;

    unsigned nVars() const { return lva.getNumVars(); }

private:
    void getReal(Real*, const PTRef);                       // Get a new real possibly using the number pool
    LVRef getLVRef(PTRef var);                              // Initialize a new LA var if needed, otherwise return the old var
    void doGaussianElimination( );                          // Performs Gaussian elimination of all redundant terms in the Tableau
    void update( LVRef, const Delta & );                    // Updates the bounds after constraint pushing
    void pivotAndUpdate( LVRef, LVRef, const Delta &);      // Updates the tableau after constraint pushing
    void getConflictingBounds( LVRef, vec<PTRef> & );       // Returns the bounds conflicting with the actual model
    void getDeducedBounds( const Delta& c, BoundT, vec<PtAsgn_reason>& dst, SolverId solver_id ); // find possible deductions by value c
    void getDeducedBounds( BoundT, vec<PtAsgn_reason>& dst, SolverId solver_id );                 // find possible deductions for actual bounds values
    void getSuggestions( vec<PTRef>& dst, SolverId solver_id );                                   // find possible suggested atoms
    void getSimpleDeductions(LVRef v, int pos);             // find deductions from actual bounds position
    unsigned getIteratorByPTRef( PTRef e, bool );                                                 // find bound iterator by the PTRef
    void refineBounds( );                                   // Compute the bounds for touched polynomials and deduces new bounds from it
    inline bool getStatus( );                               // Read the status of the solver in lbool
    inline bool setStatus( LRASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver
    void print( ostream & out );                            // Prints terms, current bounds and the tableau
    void addVarToRow( LVRef, LVRef, Real*);                 //
    bool checkIntegersAndSplit();                           //

    // Value system
    LRAModel model;
    inline void  popModel(LVRef v) { };
    const Delta& Ub(LVRef v) const;                  // The current upper bound of v
    const Delta& Lb(LVRef v) const;                  // The current lower bound of v
    bool isEquality(LVRef) const;
    const Delta overBound(LVRef) const;
    bool isModelOutOfBounds  (LVRef v) const;
    bool isModelOutOfUpperBound(LVRef v) const;
    bool isModelOutOfLowerBound(LVRef v) const;
    bool isModelInteger (LVRef v) const;

    const Delta overBound(LVRef v);
    void computeModel();                             // The implementation for the interface

    // Binded Rows system
    BindedRowStore bindedRowStore;
    inline BindedRows& getBindedRows(LVRef v) { return bra[lva[v].getBindedRowsRef()]; }
    void unbindRow(LVRef v, int row);


    // Polynomials system
    void  makePoly      (LVRef s, PTRef pol);     // Create a polynomial, introducing new LAVars if necessary
    Poly& getPoly       (LVRef s) { return pa[lva[s].getPolyRef()]; }

    // Bounds system
    vec<LABoundRefPair> ptermToLABoundRefs;
    const LABound& getBound(LVRef v, int idx) const { return ba[bla[lva[v].getBounds()][idx]]; }
    bool isUnbounded (LVRef v) const;

    bool first_update_after_backtrack;

    LRASolverStatus status;                  // Internal status of the solver (different from bool)
    vec<LVRef> LATrace;                      // The variables that have been touched
    vec<int> LATrace_lim;                    // Decision level delimiters

    // The variable system
    LVRef getNBLAVar(PTRef var);
    void addSlackVar         (PTRef leq);               // Initialize the slack var associated with lea having sum as the slack var, and cons as its bound
    void initSlackVar        ();
    LVRef getSlackVar(PTRef tr_sum, bool &reverse);
    vector < LVRef > removed_by_GaussianElimination;       // Stack of variables removed during Gaussian elimination

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
    ValPair getValue(PTRef tr);  // Computes the model and changes state.
    inline int     verbose                       ( ) const { return config.verbosity(); }
    char* printValue(PTRef tr) { char* tmp = (char*)malloc(1); tmp[0] = '\0'; return tmp; } // Implement later...
    char* printExplanation(PTRef tr) { return printValue(tr); } // Implement later...
};

#endif
