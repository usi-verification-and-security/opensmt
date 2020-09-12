#include "STPStore.h"

VertexRef STPStore::createVertex() {
    return VertexRef{vertices++};
}

EdgeRef STPStore::createEdge(VertexRef from, VertexRef to, SafeInt cost) {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.push_back(Edge{.from = from, .to = to, .neg = EdgeRef_Undef, .cost = cost, .setTime = 0});
    return r;
}

void STPStore::setNegation(EdgeRef a, EdgeRef b) {
    edges[a.x].neg = b;
    edges[b.x].neg = a;
}

void STPStore::clear() {
    edges.clear();
    vertices = 1;   // clear all vertices except zero
}

