#include "RDLTHandler.h"
#include "stpsolver/RDLSolver.h"

#include <logics/ArithLogic.h>

namespace opensmt {

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

}
