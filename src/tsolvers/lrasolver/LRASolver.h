#ifndef LRASOLVER_H
#define LRASOLVER_H

//#define GAUSSIAN_DEBUG

//#include "Timer.h"
#include "LRALogic.h"
#include "LASolver.h"

//#include "TSolver.h"
//#include "LRAModel.h"
//#include "Tableau.h"
//#include "Polynomial.h"

//#include <unordered_set>
//#include <unordered_map>

//class LAVar;
//class LAVarStore;
//class Delta;

class LRASolverStats: public LASolverStats
{
    public:
        //int num_pivot_ops;
        //int num_bland_ops;
        int num_vars;
        opensmt::OSMTTimeVal simplex_timer;

        LRASolverStats()
        : //num_pivot_ops(0)
        //, num_bland_ops(0),
          num_vars(0)
        , LASolverStats()
        {}

        void printStatistics(ostream& os) override
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

class LRASolver: public LASolver
{

private:

    LRALogic&            logic;
    //LAVarAllocator       lva;
    //LAVarStore           lavarStore;

    //LABoundAllocator     ba;
  //  LABoundListAllocator bla;
  //  LABoundStore         boundStore;


    //opensmt::Real delta; // The size of one delta.  Set through computeModel()
  //  unsigned bland_threshold;
    LRASolverStats lasolverstats;
    //void setBound(PTRef leq);

public:

    LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d);

    ~LRASolver( ) ;                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    //lbool declareTerm        (PTRef tr) override;                // Inform the theory solver about the existence of a literal
    bool  check         ( bool ) override;                  // Checks the satisfiability of current constraints
    void computeConcreteModel(LVRef v);
    void computeModel() override;
    //bool check_simplex  (bool);
    //bool  assertLit          ( PtAsgn , bool = false ) override; // Push the constraint into Solver
    //void  pushBacktrackPoint ( ) override;                       // Push a backtrack point
  //  void  popBacktrackPoint  ( ) override;                       // Backtrack to last saved point
  //  void  popBacktrackPoints  ( unsigned int ) override;         // Backtrack given number of saved points


    // Return the conflicting bounds
  //  void  getConflict(bool, vec<PtAsgn>& e) override;
  //  PtAsgn_reason getDeduction() override { if (deductions_next >= th_deductions.size()) return PtAsgn_reason_Undef; else return th_deductions[deductions_next++]; }

    LRALogic&  getLogic() override { return logic; }
  //  bool       isValid(PTRef tr) override;

#ifdef PRODUCE_PROOF
    TheoryInterpolator* getTheoryInterpolator() override { return nullptr; }
    PTRef getInterpolant( const ipartitions_t &, map<PTRef, icolor_t>* );
    bool usingStrong() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_strong; }
    bool usingWeak() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_weak; }
    bool usingFactor() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_factor; }
    const char*  getStrengthFactor() { return config.getLRAStrengthFactor(); }
#endif

protected:
    //Tableau tableau;

    //LVRef exprToLVar(PTRef expr); // Ensures this term and all variables in it has corresponding LVAR.  Returns the LAVar for the term.
  //  void pivot(LVRef basic, LVRef nonBasic);
    opensmt::Real delta;


private:

    opensmt::Real getReal(PTRef);


};

#endif
