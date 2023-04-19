/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "FSBVTHandler.h"

FSBVTHandler::FSBVTHandler(SMTConfig & c, FSBVLogic & l)
    : TSolverHandler(c)
    , logic(l)
{
}