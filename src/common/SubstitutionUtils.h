/*
* Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
*  SPDX-License-Identifier: MIT
*
*/

#ifndef OPENSMT_SUBSTITUTIONUTILS_H
#define OPENSMT_SUBSTITUTIONUTILS_H

#include "Logic.h"

void substitutionsTransitiveClosure(Logic::SubstMap & substs, Logic & logic);

#endif // OPENSMT_SUBSTITUTIONUTILS_H
