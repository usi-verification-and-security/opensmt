//
// Created by Martin Blicha on 10.05.20.
//

#include "IDLTHandler.h"
#include "stpsolver/IDLSolver.h"

#include <logics/ArithLogic.h>
#include <common/TreeOps.h>

namespace opensmt {

IDLTHandler::IDLTHandler(SMTConfig& c, ArithLogic& l)
        : TSolverHandler(c)
        , logic(l)
{
    idlsolver = new IDLSolver(config, logic);
    setSolverSchedule({idlsolver});
}

Logic &IDLTHandler::getLogic()
{
    return logic;
}

const Logic &IDLTHandler::getLogic() const
{
    return logic;
}

}
