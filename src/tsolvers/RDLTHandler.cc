#include "RDLTHandler.h"
#include "LRALogic.h"
#include "RDLSolver.h"

RDLTHandler::RDLTHandler(SMTConfig &c, LRALogic &l, TermMapper &tmap)
        : TSolverHandler(c, tmap)
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

