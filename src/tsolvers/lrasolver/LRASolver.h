#ifndef LRASOLVER_H
#define LRASOLVER_H

#include "LRALogic.h"
#include "LASolver.h"

class LRASolverStats: public LASolverStats
{
    public:

        int num_vars;
        opensmt::OSMTTimeVal simplex_timer;

        LRASolverStats()
        : LASolverStats()
        , num_vars(0)
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
    LRASolverStats lasolverstats;

public:

    LRASolver(SMTConfig & c, LRALogic & l);

    ~LRASolver( ) ;                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    TRes check         ( bool ) override;                  // Checks the satisfiability of current constraints


    LRALogic&  getLogic() override;
    lbool getPolaritySuggestion(PTRef) const;

public:
    PTRef getInterpolant( const ipartitions_t &, map<PTRef, icolor_t>* );
    PTRef getDecomposedInterpolant(const ipartitions_t & mask , map<PTRef, icolor_t> *labels);
    bool usingStrong() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_strong; }
    bool usingWeak() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_weak; }
    bool usingFactor() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_factor; }
    bool usingDecomposing() {
        return config.getLRAInterpolationAlgorithm() == itp_lra_alg_decomposing_strong ||
               config.getLRAInterpolationAlgorithm() == itp_lra_alg_decomposing_weak; }
    const char*  getStrengthFactor() { return config.getLRAStrengthFactor(); }

private:

    opensmt::Real getReal(PTRef);


};

#endif
