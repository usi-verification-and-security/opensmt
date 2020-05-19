#include "STPStore.h"

#include <utility>

VertexRef STPStore::createVertex() {
    return VertexRef{vertices++};
}

EdgeRef STPStore::createEdge(VertexRef from, VertexRef to, opensmt::Number cost) {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.push_back(Edge{.from = from, .to = to, .neg = EdgeRef_Undef, .cost = std::move(cost), .setTime = 0, .asgn = PtAsgn_Undef});
    return r;
}

void STPStore::setNegation(EdgeRef a, EdgeRef b) {
    edges[a.x].neg = b;
    edges[b.x].neg = a;
}

