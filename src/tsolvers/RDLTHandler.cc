#include "RDLTHandler.h"
#include "ArithLogic.h"
#include "RDLSolver.h"

RDLTHandler::RDLTHandler(SMTConfig &c, ArithLogic &l)
        : TSolverHandler(c)
        , logic(l)
{
    rdlsolver = new RDLSolver(config, logic);
    setSolverSchedule({rdlsolver});
}

Logic &RDLTHandler::getLogic()
{
    return logic;
}

const Logic &RDLTHandler::getLogic() const
{
    return logic;
}

