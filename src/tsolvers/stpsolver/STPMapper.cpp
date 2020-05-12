#include <Pterm.h>
#include "STPMapper.h"

STPMapper::STPMapper(LALogic const &l, STPStore &s)
    : logic(l), store(s)
{}

void STPMapper::setVert(PTRef var, VertexRef vert) {
    uint32_t idx = Idx(logic.getPterm(var).getId());
    if (varToVertRef.size() <= idx)
        varToVertRef.resize(idx + 1, VertRef_Undef);

    varToVertRef[idx] = vert;
}

void STPMapper::setEdge(PTRef leq, EdgeRef edge) {
    uint32_t idx = Idx(logic.getPterm(leq).getId());
    if (leqToEdgeRef.size() <= idx)
        leqToEdgeRef.resize(idx + 1, EdgeRef_Undef);
    leqToEdgeRef[idx] = edge;

    auto & e = store.getEdge(edge);
    if (edgesContainingVert.size() <= std::max(e.from.x, e.to.x))
        edgesContainingVert.resize(std::max(e.from.x, e.to.x) + 1);
    edgesContainingVert[e.from.x].push_back(edge);
    edgesContainingVert[e.to.x].push_back(edge);
}

EdgeRef STPMapper::getEdgeRef(PTRef leq) {
    uint32_t idx = Idx(logic.getPterm(leq).getId());
    return leqToEdgeRef.size() <= idx ? EdgeRef_Undef : leqToEdgeRef[idx];
}

