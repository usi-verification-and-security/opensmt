#include <memory>
#include "STPModel.h"

// returns a list of all vertices present in graph
vec<VertexRef> STPModel::vertsInGraph() const {
    vec<VertexRef> found;
    uint32_t n = std::min(graph.incoming.size(), graph.outgoing.size());
    uint32_t i = 0;
    // scans the incoming/outgoing vectors to see if they contain edges
    for (; i < n; ++i) {
        if (graph.incoming[i].size() || graph.outgoing[i].size())
            found.push(VertexRef{.x = i});
    }
    const vec<vec<EdgeRef>> &rest = (n == graph.incoming.size()) ? graph.outgoing : graph.incoming;
    for (; i < rest.size(); ++i) {
        if (rest[i].size())
            found.push(VertexRef{.x = i});
    }

    return found;
}

// creates a common point from which to start the search, and connects it to all vertices in graph
VertexRef STPModel::addStartingPoint() {
    VertexRef start = store.createVertex();

    for (VertexRef v : vertsInGraph()) {
        EdgeRef eRef = store.createEdge(start, v, 0);
        graph.addEdge(eRef, start, v);
    }

    return start;
}

void STPModel::bellmanFord(VertexRef start) {
    std::unordered_map<uint32_t, ptrdiff_t> dist;
    std::queue<VertexRef> open;
    dist.emplace(start.x, 0);
    open.push(start);

    while (!open.empty()) {
        VertexRef v = open.front(); open.pop();
        for (auto eRef : graph.outgoing[v.x]) {
            const Edge &edge = store.getEdge(eRef);
            if (!dist.count(edge.to.x) || dist[edge.to.x] > dist[v.x] + edge.cost) {
                dist[edge.to.x] = dist[v.x] + edge.cost;
                open.push(edge.to);
            }
        }
    }

    valMap = std::move(dist);
}

// shifts 'valMap' values so that valMap[zero] == 0
void STPModel::shiftZero() {
    VertexRef zero = store.zero();
    if (!valMap.count(zero.x)) return; // if 'zero' isn't present, no need to shift anything
    ptrdiff_t shift = valMap[zero.x];
    for (auto &pair : valMap) {
        pair.second -= shift;
    }
    assert( valMap[zero.x] == 0 );
    vec<int> a;
    a.copyTo(a);
}

void STPModel::createModel() {
    VertexRef start = addStartingPoint();
    bellmanFord(start);
    shiftZero();
}