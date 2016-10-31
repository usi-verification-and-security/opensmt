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

#include "LRALogic.h"
#include "TSolver.h"
#include "LAVar.h"

class LRASolverStats: public TSolverStats
{
    public:
        int num_pivot_ops;
        int num_bland_ops;
        int num_vars;

        LRASolverStats()
        : num_pivot_ops(0)
        , num_bland_ops(0)
        , num_vars(0)
        { TSolverStats(); }

        void printStatistics(ostream& os)
        {
            cerr << "; -------------------------" << endl;
            cerr << "; STATISTICS FOR LRA SOLVER" << endl;
            cerr << "; -------------------------" << endl;
            TSolverStats::printStatistics(os);
            os << "; Number of LRA vars.......: " << num_vars << endl;
            os << "; Pivot operations.........: " << num_pivot_ops << endl;
            os << "; Bland operations.........: " << num_bland_ops << endl;
        }
};

//
// Class to solve Linear Arithmetic theories
//

class LRASolver: public TSolver
{
private:

    vector<Real*> numbers_pool;             // Collect numbers (useful for removal)
    LRALogic& logic;
    LAVarStore* lavarStore;
    // Structure to keep backtracking history elements
    class LAVarHistory
    {
    public:
        PTRef e;
        LAVar * v;
        unsigned bound;
        BoundT bound_type;
        LAVarHistory() : e(PTRef_Undef), v(NULL), bound_type(bound_n), bound(0) {}
    };

    // Possible internal states of the solver
    typedef enum
    {
        INIT, INCREMENT, SAT, UNSAT, ERROR
    } LRASolverStatus;

    typedef vector<LAVar *> VectorLAVar;

    opensmt::Real delta; // The size of one delta.  Set through computeModel()
    unsigned bland_threshold;
    LRASolverStats tsolver_stats;
    void initSlackVar(LAVar* s);
    void setBound(PTRef leq);
public:

    LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d);

    ~LRASolver( );                                      // Destructor ;-)

    virtual void clearSolver(); // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    LAVar* getSlackVar       (PTRef tr_sum, bool& reverse); // Get a slack var for the sum term, creating it if it does not exist.  If there exists a slack var for the negation of tr_sum, set reverse to true
    void addSlackVar         (PTRef leq);               // Initialize the slack var associated with lea having sum as the slack var, and cons as its bound
    void makePolynomial      (LAVar *s, PTRef pol);     // Create a polynomial, introducing new LAVars if necessary, for the slack var.  Can this be moved to LAVarStore?
    void initSlackVar        ();
    lbool declareTerm        (PTRef tr);                // Inform the theory solver about the existence of a literal
    bool  check              ( bool );                  // Checks the satisfiability of current constraints
    bool  assertLit          ( PtAsgn , bool = false ); // Push the constraint into Solver
    void  pushBacktrackPoint ( );                       // Push a backtrack point
    void  popBacktrackPoint  ( );                       // Backtrack to last saved point
    void  computeModel       ( );                       // Computes the model into enodes

    void  getConflict(bool, vec<PtAsgn>& e) { for (int i = 0; i < explanation.size(); i++) { e.push(explanation[i]); } } // Return the conflicting bounds
    PtAsgn_reason getDeduction() { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

    LRALogic&  getLogic() { return logic; }
    const void getRemoved(vec<PTRef>&) const;  // Fill the vector with the vars removed due to not having bounds

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

    VectorLAVar columns;                 // Maps terms' ID to LAVar pointers
    VectorLAVar rows;                    // Maps terms' ID to LAVar pointers, used to store basic columns
    VectorLAVar ptermToLavar;            // Maps original constraints to solver's terms and bounds.  Could this be moved to LAVarStore?

    bool assertBoundOnColumn( LAVar * it, unsigned it_i);

    vector<unsigned> checks_history;

    unsigned nVars() const { return columns.size() - removed_by_GaussianElimination.size(); }
private:
    void getReal(Real*, const PTRef);                       // Get a new real possibly using the number pool
    LAVar *getLAVar(PTRef var);                             // Initialize a new LA var if needed, otherwise return the old var
    void doGaussianElimination( );                          // Performs Gaussian elimination of all redundant terms in the Tableau
    void update( LAVar *, const Delta & );                  // Updates the bounds after constraint pushing
    void pivotAndUpdate( LAVar *, LAVar *, const Delta &);  // Updates the tableau after constraint pushing
    void getConflictingBounds( LAVar *, vec<PTRef> & );     // Returns the bounds conflicting with the actual model
    void refineBounds( );                                   // Compute the bounds for touched polynomials and deduces new bounds from it
    inline bool getStatus( );                               // Read the status of the solver in lbool
    inline bool setStatus( LRASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver
    void print( ostream & out );                            // Prints terms, current bounds and the tableau
    void addVarToRow( LAVar*, LAVar*, Real*);               //
    bool checkIntegersAndSplit();                           //

    bool first_update_after_backtrack;

    LRASolverStatus status;                  // Internal status of the solver (different from bool)
    vector<LAVarHistory> pushed_constraints; // Keeps history of constraints
    set<LAVar *> touched_rows;               // Keeps the set of modified rows

    vector < LAVar * > removed_by_GaussianElimination;       // Stack of variables removed during Gaussian elimination

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

    ValPair getValue(PTRef tr) const; // Computes the model and changes state.
    inline int     verbose                       ( ) const { return config.verbosity(); }
    char* printValue(PTRef tr) { char* tmp = (char*)malloc(1); tmp[0] = '\0'; return tmp; } // Implement later...
    char* printExplanation(PTRef tr) { return printValue(tr); } // Implement later...
};

#endif
