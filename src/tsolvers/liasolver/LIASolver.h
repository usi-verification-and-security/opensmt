#ifndef LIASOLVER_H
#define LIASOLVER_H

#include "LIALogic.h"
#include "LASolver.h"
#include "lasolver/LARefs.h"



class LIASolverStats: public LASolverStats
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

    LIALogic&            logic;
    LIASolverStats lasolverstats;


public:

    LIASolver(SMTConfig & c, LIALogic& l, vec<DedElem>& d);

    ~LIASolver( );                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    LIALogic&  getLogic() override;// { return logic; }
    TRes check    ( bool complete) override; // Checks the satisfiability of current constraints //PS. add the implementation to LIASolver.C
    void getNewSplits(vec<PTRef>& splits) override;

protected:

    void notifyVar(LVRef v) override;
    void initSolver( );                                     // Initializes the solver

    TRes checkIntegersAndSplit();
    bool isModelInteger (LVRef v) const;



    opensmt::Integer2 getInt(PTRef r) ;

    Map<LVRef, bool, LVRefHash> int_vars_map; // stores problem variables for duplicate check
    vec<LVRef> int_vars;                      // stores the list of problem variables without duplicates
    vec<Map<opensmt::Real, bool, FastRationalHash> > cuts;

};

#endif
