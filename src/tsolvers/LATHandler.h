//
// Created by Antti on 21.10.21.
//

#ifndef OPENSMT_LATHANDLER_H
#define OPENSMT_LATHANDLER_H

#include "TSolverHandler.h"
#include "ArithLogic.h"
#include "LASolver.h"

class LATHandler : public TSolverHandler
{
private:
    ArithLogic & logic;
    LASolver * lasolver;
public:
    LATHandler(SMTConfig & c, ArithLogic & l);
    virtual ~LATHandler() = default;
    virtual Logic & getLogic() override { return logic; }
    virtual Logic const & getLogic() const override { return logic; }
    virtual lbool getPolaritySuggestion(PTRef p) const override { return lasolver->getPolaritySuggestion(p); }

    virtual PTRef getInterpolant(ipartitions_t const & mask, map<PTRef, icolor_t> * labels, PartitionManager & pmanager) override;
};

#endif //OPENSMT_LATHANDLER_H
