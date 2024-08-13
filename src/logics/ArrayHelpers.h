/*
 *  Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */
#ifndef OPENSMT_ARRAYHELPERS_H
#define OPENSMT_ARRAYHELPERS_H

#include "Logic.h"

namespace opensmt {

PTRef instantiateReadOverStore(Logic & logic, PTRef fla);

vec<PTRef> collectStores(Logic const & logic, PTRef fla);

}

#endif //OPENSMT_ARRAYHELPERS_H
