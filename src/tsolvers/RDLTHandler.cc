#include "RDLTHandler.h"
#include "ArithLogic.h"
#include "RDLSolver.h"

RDLTHandler::RDLTHandler(SMTConfig &c, ArithLogic &l)
        : TSolverHandler(c)
        , logic(l)
{
    rdlsolver = new RDLSolver(config, logic);
    SolverId my_id = rdlsolver->getId();
    tsolvers[my_id.id] = rdlsolver;
    solverSchedule.push(my_id.id);
}

Logic &RDLTHandler::getLogic()
{
    return logic;
}

const Logic &RDLTHandler::getLogic() const
{
    return logic;
}

