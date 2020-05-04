#include "STPStore.h"

#include <utility>

VertexRef STPStore::createVertex() {
    // create new vertex ref
    uint32_t i = verts.size();
    VertexRef r{i};
    verts.push_back(r);

    // allocate memory for adjancency lists
    incoming.emplace_back();
    outgoing.emplace_back();

    return r;
}

EdgeRef STPStore::createEdge(VertexRef from, VertexRef to, opensmt::Number cost) {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.push_back(Edge{from, to, EdgeRef_Undef, std::move(cost)});
    return r;
}

void STPStore::setNegation(EdgeRef a, EdgeRef b) {
    edges[a.x].neg = b;
    edges[b.x].neg = a;
}

EdgeRef STPStore::hasNeighbour(VertexRef from, VertexRef to) {
    for (auto && e : outgoing[from.x]) {
        if (edges[e.x].to == to) return e;
    }
    return EdgeRef_Undef;
}