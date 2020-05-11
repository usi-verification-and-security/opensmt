#include <stack>
#include "STPEdgeGraph.h"

bool STPEdgeGraph::isTrue(EdgeRef e) {
    // TODO
    return false;
}

void STPEdgeGraph::setTrue(EdgeRef e) {
    // TODO
}

void STPEdgeGraph::getConsequences(EdgeRef e) {
    size_t n = store.vertexNum();
    std::vector<opensmt::Number> aCosts(n), bCosts(n);
    auto edge = store.getEdge(e);

    std::vector<opensmt::Number> visited(n);

    std::stack<VertexRef> open;
    while (!open.empty()) {
        auto current = open.top(); open.pop();
        auto currCost = visited[current.x];
        for (EdgeRef pRef : incoming[current.x]) {
            Edge & path = store.getEdge(pRef);
            auto & cand = visited[path.from.x];
            if (cand > currCost + path.cost) {
                cand = currCost + path.cost;
                open.push(path.from);
            }
        }
    }

    // TODO ...
}


