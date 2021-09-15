//
// Created by Martin Blicha on 10.05.20.
//

#include "IDLTHandler.h"
#include "ArithLogic.h"
#include "IDLSolver.h"
#include "TreeOps.h"

IDLTHandler::IDLTHandler(SMTConfig& c, ArithLogic& l)
        : TSolverHandler(c)
        , logic(l)
{
    idlsolver = new IDLSolver(config, logic);
    SolverId my_id = idlsolver->getId();
    tsolvers[my_id.id] = idlsolver;
    solverSchedule.push(my_id.id);
}

Logic &IDLTHandler::getLogic()
{
    return logic;
}

const Logic &IDLTHandler::getLogic() const
{
    return logic;
}