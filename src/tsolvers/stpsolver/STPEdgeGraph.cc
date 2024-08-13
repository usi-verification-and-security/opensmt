#include "STPEdgeGraph.h"

namespace opensmt {
void EdgeGraph::addEdge(EdgeRef e, VertexRef from, VertexRef to) {
    auto max = std::max(from.x, to.x);
    if (incoming.size() <= max) {
        incoming.resize(max + 1);
        outgoing.resize(max + 1);
    }
    addedEdges.push_back(e);
    incoming[to.x].push_back(e);
    outgoing[from.x].push_back(e);
}

void EdgeGraph::clear() {
    addedEdges.clear();
    incoming.clear();
    outgoing.clear();
}

bool EdgeGraph::isEmpty() const {
    assert(incoming.size() == outgoing.size());
    return incoming.empty();
}
} // namespace opensmt
