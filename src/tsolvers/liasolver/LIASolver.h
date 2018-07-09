#ifndef LIASOLVER_H
#define LIASOLVER_H

//#define GAUSSIAN_DEBUG


#include "LIALogic.h"
#include "LASolver.h"
#include "lrasolver/LARefs.h"



class LIASolverStats: public LASolverStats  //PS. check all opensmt::real and should I change them to opensmt::integer
{
public:

    int num_vars;
    opensmt::OSMTTimeVal bb_timer;

    LIASolverStats()
            : num_vars(0)
            , LASolverStats()
    {}

    void printStatistics(ostream& os) override
    {
        os << "; -------------------------" << endl;
        os << "; STATISTICS FOR LIA SOLVER" << endl;
        os << "; -------------------------" << endl;
        LASolverStats::printStatistics(os);
        os << "; Number of LIA vars.......: " << num_vars << endl;
        //os << "; Pivot operations.........: " << num_pivot_ops << endl;
        //os << "; Bland operations.........: " << num_bland_ops << endl;
        os << "; BB time.............: " << bb_timer.getTime() << " s\n";
    }
};


//
// Class to solve Linear Arithmetic theories
//

class LIASolver: public LASolver
{
private:

    struct LVRefPair { LVRef p1; LVRef p2; };
//    vector<opensmt::Real*> numbers_pool;    // Collect numbers.  Should work as a simple memory managemet system
    LIALogic&            logic; //PS. shall I declare logic as LIA?
    LIASolverStats lasolverstats;


public:

    LIASolver(SMTConfig & c, LIALogic& l, vec<DedElem>& d);

    ~LIASolver( );                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    LIALogic&  getLogic() override;// { return logic; }
    bool  check    ( bool complete) override; // Checks the satisfiability of current constraints //PS. add the implementation to LIASolver.C
    void computeConcreteModel(LVRef v);
    void computeModel() override;

protected:

    Polynomial expressionToLVarPoly(PTRef expression) override;


    //inline bool setStatus( LASolverStatus );               // Sets and return status of the solver //PS. use only LASolverStats
    void initSolver( );                                     // Initializes the solver

//    void addVarToRow( LVRef, LVRef, opensmt::Real*);
    bool checkIntegersAndSplit();                           //
    bool isModelInteger (LVRef v) const;
   // extern inline bool setStatus( LASolverStatus ) override;

    //LASolverStatus status;                  // Internal status of the solver (different from bool)

    opensmt::Integer2 getInt(PTRef r) ;

    Map<LVRef, bool, LVRefHash> int_vars; //stores problem variables

};

#endif
