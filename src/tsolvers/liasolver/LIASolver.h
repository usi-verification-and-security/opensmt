#ifndef LIASOLVER_H
#define LIASOLVER_H

#include "LIALogic.h"
#include "LASolver.h"
#include "lasolver/LARefs.h"
#include <unordered_map>
#include <vector>

#include <map>

//
// Class to solve Linear Arithmetic theories
//

class LIASolver: public LASolver
{
private:

    LIALogic&            logic;


public:

    LIASolver(SMTConfig & c, LIALogic & l);

    ~LIASolver() = default;

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    LIALogic& getLogic() override { return logic; }
    TRes check(bool complete) override;
    void getNewSplits(vec<PTRef>& splits) override;

    PTRef getInterpolant(std::map<PTRef, icolor_t> const&);

protected:

    void notifyVar(LVRef v) override;

    TRes checkIntegersAndSplit();
    bool isModelInteger (LVRef v) const;

    virtual bool isIntVar(LVRef v) const override { return int_vars_map.has(v); }
    virtual void markVarAsInt(LVRef v) override;


    FastRational getInt(PTRef r) ;

    Map<LVRef, bool, LVRefHash> int_vars_map; // stores problem variables for duplicate check
    vec<LVRef> int_vars;                      // stores the list of problem variables without duplicates
    std::vector<std::unordered_map<opensmt::Real, bool, FastRationalHash> > cuts;

};

#endif
