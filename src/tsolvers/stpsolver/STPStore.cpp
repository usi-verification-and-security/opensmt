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

EdgeRef STPStore::createEdge() {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.push_back(r);
    costs.emplace_back();
    return r;
}