#ifndef OPENSMT_STPMAPPER_H
#define OPENSMT_STPMAPPER_H

#include <vector>
#include <LALogic.h>
#include "STPStore.h"


class STPMapper {
    LALogic &logic;

    STPStore &store;

    std::vector<VertexRef> varToVertRef;
    std::vector<EdgeRef> leqToEdgeRef;

public:
    STPMapper(const LALogic &l, STPStore &s);
};

#endif //OPENSMT_STPMAPPER_H
