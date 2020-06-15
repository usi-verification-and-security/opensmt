#ifndef LASOLVER_H
#define LASOLVER_H

//#define GAUSSIAN_DEBUG

#include "Timer.h"
#include "LALogic.h"

#include "TSolver.h"
#include "lrasolver/LRAModel.h"
#include "Tableau.h"
#include "Polynomial.h"
#include "Simplex.h"

#include <unordered_map>
#include "LAVarMapper.h"

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
        : TSolverStats()
        , num_pivot_ops(0)
        , num_bland_ops(0)
        , num_vars(0)
        {}

        void printStatistics(ostream& os) override
        {
            os << "; -------------------------" << endl;
            os << "; STATISTICS FOR LA SOLVER" << endl;
            os << "; -------------------------" << endl;
            TSolverStats::printStatistics(os);
            os << "; Number of LA vars........: " << num_vars << endl;
            os << "; LA time..................: " << timer.getTime() << " s\n";
        }
};


//
// Class to solve Linear Arithmetic theories
//

class LASolver: public TSolver
{

protected:
    struct DecEl { PtAsgn asgn; int dl; };

    LALogic&             logic;
    LAVarStore           laVarStore;
    LAVarMapper          laVarMapper;
    LABoundStore         boundStore;
    Simplex              simplex;
    vec<PtAsgn>          decision_trace;
    vec<int>             dec_limit;
    vec<DecEl>           int_decisions;

    PtAsgn               popTermBacktrackPoint();
    PtAsgn               popDecisions();
    void                 pushDecision(PtAsgn);
    int                  backtrackLevel();

    std::vector<opensmt::Real> explanationCoefficients;

    vec<PtAsgn>          LABoundRefToLeqAsgn;
    PtAsgn getAsgnByBound(LABoundRef br) const;
    vec<LABoundRefPair>  LeqToLABoundRefPair;
    LABoundRefPair getBoundRefPair(const PTRef leq) const
        { return LeqToLABoundRefPair[Idx(logic.getPterm(leq).getId())]; }

    // Possible internal states of the solver
    typedef enum
    {
        INIT, INCREMENT, SAT, UNSAT, NEWSPLIT, UNKNOWN, ERROR
    } LASolverStatus;

    //opensmt::Real delta; // The size of one delta.  Set through computeModel()
    LASolverStats tsolver_stats;
    void setBound(PTRef leq);
    bool assertBoundOnVar(LVRef it, LABoundRef itBound_ref);

protected:
    PTRef getVarPTRef(LVRef v) const {
        return laVarMapper.getVarPTRef(v);
    }

public:

    LASolver(SolverDescr dls, SMTConfig & c, LALogic & l);

    virtual ~LASolver( );                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    void  declareAtom        (PTRef tr) override;                // Inform the theory solver about the existence of an atom
    void  informNewSplit     (PTRef tr) override;                // Update bounds for the split variable
    bool  check_simplex      (bool);
    bool  assertLit          ( PtAsgn ) override;                // Push the constraint into Solver
    void  pushBacktrackPoint ( ) override;                       // Push a backtrack point
    void  popBacktrackPoint  ( ) override;                       // Backtrack to last saved point
    void  popBacktrackPoints ( unsigned int ) override;         // Backtrack given number of saved points


    // Return the conflicting bounds
    void          getConflict(bool, vec<PtAsgn>& e) override;

    LALogic&   getLogic() override;
    bool       isValid(PTRef tr) override;


protected:

    LABoundStore::BoundInfo addBound(PTRef leq_tr);
    void updateBound(PTRef leq_tr);
    LVRef exprToLVar(PTRef expr); // Ensures this term and all variables in it has corresponding LVAR.  Returns the LAVar for the term.
    void storeExplanation(Simplex::Explanation &&explanationBounds);

    std::unique_ptr<Polynomial> expressionToLVarPoly(PTRef term);

    opensmt::Number getNum(PTRef);

    virtual bool isIntVar(LVRef v) const { return false; }
    virtual void markVarAsInt(LVRef v) {/* do nothing as default */}
    // Compute the values for an upper bound v ~ c and its negation \neg (v ~ c), where ~ is < if strict and <= if !strict
    LABoundStore::BoundValuePair getBoundsValue(LVRef v, const Real & c, bool strict);
    LABoundStore::BoundValuePair getBoundsValueForIntVar(const Real & c, bool strict);
    LABoundStore::BoundValuePair getBoundsValueForRealVar(const Real & c, bool strict);

    LVRef getLAVar_single(PTRef term);                      // Initialize a new LA var if needed, otherwise return the old var
    bool hasVar(PTRef expr);
    LVRef getVarForLeq(PTRef ref)  const  { return laVarMapper.getVarByLeqId(logic.getPterm(ref).getId()); }
    LVRef getVarForTerm(PTRef ref) const  { return laVarMapper.getVarByPTId(logic.getPterm(ref).getId()); }
    virtual void notifyVar(LVRef) {}                             // Notify the solver of the existence of the var. This is so that LIA can add it to integer vars list.
    void getSuggestions( vec<PTRef>& dst, SolverId solver_id );                                   // find possible suggested atoms
    void getSimpleDeductions(LVRef v, LABoundRef);      // find deductions from actual bounds position
    unsigned getIteratorByPTRef( PTRef e, bool );                                                 // find bound iterator by the PTRef
    inline bool getStatus( );                               // Read the status of the solver in lbool
    bool setStatus( LASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver

    void computeConcreteModel(LVRef v, const opensmt::Real& d);
    void computeModel() override;

    void print( ostream & out ) override;                            // Prints terms, current bounds and the tableau


    Delta evalSum(PTRef tr) const;
    std::vector<opensmt::Real> concrete_model;              // Save here the concrete model for the vars indexed by Id
//    const Delta overBound(LVRef v);
//    bool isModelOutOfBounds(LVRef v) const;

    opensmt::Real evaluateTerm(PTRef tr);

    LASolverStatus status;                  // Internal status of the solver (different from bool)


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
    void fillTheoryVars(ModelBuilder & modelBuilder) const override;

    inline int     verbose                       ( ) const { return config.verbosity(); }

    // Debug stuff
    void isProperLeq(PTRef tr);  // The Leq term conforms to the assumptions of its form.  Only asserts.
    void crashInconsistency(LVRef v, int line);

    void deduce(LABoundRef bound_prop);
};

#endif
