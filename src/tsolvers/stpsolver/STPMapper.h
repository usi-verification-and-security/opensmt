#ifndef OPENSMT_STPMAPPER_H
#define OPENSMT_STPMAPPER_H

#include <vector>
#include <LALogic.h>
#include <Pterm.h>
#include "STPStore.h"


class STPMapper {
    LALogic const &logic;

    STPStore &store;

    std::vector<VertexRef> varToVertRef;              // maps PTRefs of variables to VertRefs
    std::vector<EdgeRef> leqToEdgeRef;                // maps PTRefs of inequalities to EdgeRefs
    std::vector<std::vector<EdgeRef>> edgesContainingVert;

public:
    STPMapper(LALogic const &l, STPStore &s);
    void setVert(PTRef var, VertexRef vert);
    void setEdge(PTRef leq, EdgeRef edge);
    EdgeRef getEdgeRef(PTRef leq);
    const vector<EdgeRef> & edgesOf(VertexRef v) { return edgesContainingVert[v.x]; }
};

#endif //OPENSMT_STPMAPPER_H
