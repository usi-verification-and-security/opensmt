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
        : num_vars(0)
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
    LRASolverStats lasolverstats;

public:

    LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d);

    ~LRASolver( ) ;                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    TRes check         ( bool ) override;                  // Checks the satisfiability of current constraints
    void computeConcreteModel(LVRef v);
    void computeModel() override;

    LRALogic&  getLogic() override;
    lbool getPolaritySuggestion(PTRef) const;


#ifdef PRODUCE_PROOF
    PTRef getInterpolant( const ipartitions_t &, map<PTRef, icolor_t>* );
    PTRef getExperimentalInterpolant( const ipartitions_t & mask , map<PTRef, icolor_t> *labels);
    bool usingStrong() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_strong; }
    bool usingWeak() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_weak; }
    bool usingFactor() { return config.getLRAInterpolationAlgorithm() == itp_lra_alg_factor; }
    bool usingExperimental() {
        return config.getLRAInterpolationAlgorithm() == itp_lra_alg_experimental_strong ||
               config.getLRAInterpolationAlgorithm() == itp_lra_alg_experimental_weak; }
    const char*  getStrengthFactor() { return config.getLRAStrengthFactor(); }

    struct InterpolStatistics{
        std::size_t interestingInterpolants = 0;
        std::size_t defaultInterpolants = 0;

        void print(std::ostream& os){
            os << "; -----------------------------------" << '\n';
            os << "; LRA SOLVER INTERPOLATION STATISTICS" << '\n';
            os << "; -----------------------------------" << '\n';
            os << "; Number of interesting interpolation produced: " << interestingInterpolants << '\n';
            os << "; Number of default interpolation produced: " << defaultInterpolants << '\n';
        }
    };

    InterpolStatistics interpolStats;
#endif

protected:

    opensmt::Real delta;
    void doGaussianElimination() override;

private:

    opensmt::Real getReal(PTRef);


};

#endif
