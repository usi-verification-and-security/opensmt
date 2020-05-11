#include "STPStore.h"

#include <utility>

VertexRef STPStore::createVertex() {
    // create new vertex ref
    uint32_t i = verts.size();
    VertexRef r{i};
    verts.push_back(r);
    edgesOfVertex.emplace_back();

    return r;
}

EdgeRef STPStore::createEdge(VertexRef from, VertexRef to, opensmt::Number cost) {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.push_back(Edge{from, to, EdgeRef_Undef, std::move(cost)});
    edgesOfVertex[from.x].push_back(r);
    edgesOfVertex[to.x].push_back(r);
    return r;
}

void STPStore::setTrue(EdgeRef e) {
    auto edge = getEdge(e);
}

void STPStore::setNegation(EdgeRef a, EdgeRef b) {
    edges[a.x].neg = b;
    edges[b.x].neg = a;
}

