#include "STPStore.h"

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
    edges.push_back(Edge{from, to});
    costs.push_back(cost);
    return r;
}