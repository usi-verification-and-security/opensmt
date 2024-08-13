/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArrayTHandler.h"
#include "egraph/InterpolatingEgraph.h"

namespace opensmt {

ArrayTHandler::ArrayTHandler(SMTConfig & c, Logic & l)
        : TSolverHandler(c)
        , logic(l)
{
    egraph = config.produce_inter() ? new InterpolatingEgraph(config, logic)
                                    : new Egraph(config, logic);

    arraySolver = new ArraySolver(logic, *egraph, c);
    setSolverSchedule({egraph, arraySolver});
}

}
