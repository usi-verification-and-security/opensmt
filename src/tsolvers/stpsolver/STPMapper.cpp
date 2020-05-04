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
    if (vertsToEdgeRef.size() <= e.to.x)
        vertsToEdgeRef.resize(e.to.x + 1);
    if (vertsToEdgeRef[e.to.x].size() <= e.from.x)
        vertsToEdgeRef[e.to.x].resize(e.from.x, EdgeRef_Undef);
    vertsToEdgeRef[e.to.x][e.from.x] = edge;
}

EdgeRef STPMapper::getEdgeRef(PTRef leq) {
    uint32_t idx = Idx(logic.getPterm(leq).getId());
    return leqToEdgeRef.size() <= idx ? EdgeRef_Undef : leqToEdgeRef[idx];
}

EdgeRef STPMapper::getEdgeRef(VertexRef x, VertexRef y) {
    if (vertsToEdgeRef.size() <= x.x) return EdgeRef_Undef;
    auto &xE = vertsToEdgeRef[x.x];
    return xE.size() <= y.x ? EdgeRef_Undef : xE[y.x];
}