#include <Pterm.h>
#include "STPMapper.h"

STPMapper::STPMapper(LALogic const &l, STPStore &s)
    : logic(l), store(s)
{}

// assigns a VertexRef to a PTRef variable
void STPMapper::setVert(PTRef var, VertexRef vert) {
    uint32_t idx = Idx(logic.getPterm(var).getId());
    if (varToVertRef.size() <= idx)
        varToVertRef.resize(idx + 1, VertRef_Undef);

    varToVertRef[idx] = vert;
}

// adds an EdgeRef to the 'edgesOf' lists of its vertices
void STPMapper::registerEdge(EdgeRef edge) {
    auto & e = store.getEdge(edge);
    if (edgesContainingVert.size() <= std::max(e.from.x, e.to.x))
        edgesContainingVert.resize(std::max(e.from.x, e.to.x) + 1);
    edgesContainingVert[e.from.x].push_back(edge);
    edgesContainingVert[e.to.x].push_back(edge);
}

// assigns an EdgeRef to a PTRef inequality and adds it to the 'edgesOf' lists of its vertices
void STPMapper::mapEdge(PTRef leq, EdgeRef edge) {
    registerEdge(edge);

    uint32_t idx = Idx(logic.getPterm(leq).getId());
    if (leqToEdgeRef.size() <= idx)
        leqToEdgeRef.resize(idx + 1, EdgeRef_Undef);
    leqToEdgeRef[idx] = edge;
}

// returns the VertexRef corresponding to a PTRef, if it exists
VertexRef STPMapper::getVertRef(PTRef var) {
    uint32_t idx = Idx(logic.getPterm(var).getId());
    return varToVertRef.size() <= idx ? VertRef_Undef : varToVertRef[idx];
}

// returns the EdgeRef corresponding to a PTRef, if it exists
EdgeRef STPMapper::getEdgeRef(PTRef leq) {
    uint32_t idx = Idx(logic.getPterm(leq).getId());
    return leqToEdgeRef.size() <= idx ? EdgeRef_Undef : leqToEdgeRef[idx];
}

// returns a registered EdgeRef corresponding to these parameters, if it exists
EdgeRef STPMapper::getEdgeRef(VertexRef y, VertexRef x, const opensmt::Number &c) const {
    if (y == VertRef_Undef || x == VertRef_Undef) return EdgeRef_Undef;

    // scans through all edges of y to find the one matching our parameters
    // only used in 'declareAtom' to look for negations, so we don't mind the linear time as much
    auto &possible = edgesContainingVert[y.x];
    for (EdgeRef eRef : possible) {
        auto &edge = store.getEdge(eRef);
        if (edge.from == y && edge.to == x && edge.cost == c) return eRef;
    }
    return EdgeRef_Undef;
}

