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

    void setVert(PTRef var, VertexRef vert);
    void setEdge(PTRef leq, EdgeRef edge);
};

#endif //OPENSMT_STPMAPPER_H
