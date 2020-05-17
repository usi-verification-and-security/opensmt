#include "STPStore.h"

#include <utility>

VertexRef STPStore::createVertex() {
    // create new vertex ref
    return VertexRef{vertices++};
}

EdgeRef STPStore::createEdge(VertexRef from, VertexRef to, opensmt::Number cost) {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.push_back(Edge{from, to, EdgeRef_Undef, std::move(cost), 0});
    return r;
}

void STPStore::setNegation(EdgeRef a, EdgeRef b) {
    edges[a.x].neg = b;
    edges[b.x].neg = a;
}

