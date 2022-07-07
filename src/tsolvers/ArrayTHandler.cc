/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArrayTHandler.h"

#include "InterpolatingEgraph.h"

ArrayTHandler::ArrayTHandler(SMTConfig & c, Logic & l)
        : TSolverHandler(c)
        , logic(l)
{
    egraph = config.produce_inter() > 0 ? new InterpolatingEgraph(config, logic)
                                        : new Egraph(config, logic);

    SolverId my_id = egraph->getId();
    tsolvers[my_id.id] = egraph;
    solverSchedule.push(my_id.id);

    arraySolver = new ArraySolver(logic, *egraph, c);
    my_id = arraySolver->getId();
    tsolvers[my_id.id] = arraySolver;
    solverSchedule.push(my_id.id);
}
