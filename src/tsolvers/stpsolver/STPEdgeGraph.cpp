#include <stack>
#include "STPEdgeGraph.h"

bool STPEdgeGraph::isTrue(EdgeRef e) const {
    return e != EdgeRef_Undef && store.getEdge(e).setTime != 0;
}

void STPEdgeGraph::setTrue(EdgeRef e, bool consequence) {
    Edge &edge = store.getEdge(e);
    if (edge.setTime != 0) return;              // edge was already set to true - it is already stored

    if (!consequence) ++addedCount;             // consequences have the same timestamp as the edge that caused them
    addedEdges.push_back(e);
    edge.setTime = addedCount;
    auto max = std::max(edge.from.x, edge.to.x);
    if (incoming.size() <= max) {
        incoming.resize(max + 1);
        outgoing.resize(max + 1);
    }
    outgoing[edge.from.x].push_back(e);
    incoming[edge.to.x].push_back(e);
}

// Searches through the graph to find consequences of currently assigned edges, starting from 'e'
void STPEdgeGraph::findConsequences(EdgeRef e) {
    size_t n = store.vertexNum();

    std::vector<bool> visitedA(n), visitedB(n);             // maps which vertex was visited in DFS TODO: Replace with maps?
    std::vector<opensmt::Number> lengthA(n), lengthB(n);    // maps the lowest distance found from start to a vertex

    auto start = store.getEdge(e);
    // find potential starts/ends of an edge
    auto aTotal = dfsSearch(start.from, visitedA, lengthA, false);
    auto bTotal = dfsSearch(start.to, visitedB, lengthB, true);

    // we scan through the side which appears in fewer total edges
    bool aLess = aTotal <= bTotal;
    auto &thisVisited = aLess ? visitedA : visitedB;
    auto &otherVisited = aLess ? visitedB : visitedA;
    auto &thisLength = aLess ? lengthA : lengthB;
    auto &otherLength = aLess ? lengthB : lengthA;

    // for each (WLOG) 'a', go through its edges and find each 'a -> b' edge that has cost higher than length found by DFS
    // such edges are consequences of the current graph
    for (uint32_t i = 0; i < n; ++i) {
        if (!thisVisited[i]) continue;
        for (auto eRef : mapper.edgesOf(VertexRef{i})) {
            Edge &edge = store.getEdge(eRef);
            auto thisSide = aLess ? edge.from.x : edge.to.x;
            auto otherSide = aLess ? edge.to.x : edge.from.x;
            if (thisSide == i && otherVisited[otherSide] && edge.cost >= thisLength[thisSide] + start.cost + otherLength[otherSide])
                setTrue(eRef, true);
        }
    }
}

// DFS through the graph to find shortest paths to all reachable vertices from 'init' in the given direction
size_t STPEdgeGraph::dfsSearch(VertexRef init, std::vector<bool> &visited, std::vector<opensmt::Number> &length, bool forward) {
    size_t total = 0;
    std::stack<VertexRef> open;
    visited[init.x] = true;
    length[init.x] = 0;
    open.push(init);

    while (!open.empty()) {
        VertexRef curr = open.top(); open.pop();
        auto &toScan = forward ? outgoing[curr.x] : incoming[curr.x];
        for (auto eRef : toScan) {
            Edge &edge = store.getEdge(eRef);
            auto next = forward ? edge.to : edge.from;
            if (!visited[next.x]) {
                visited[next.x] = true;
                open.push(next);
                length[next.x] = length[curr.x] + edge.cost;
                total += static_cast<uint32_t>(mapper.edgesOf(next).size());
            } else if (length[next.x] > length[curr.x] + edge.cost) {
                length[next.x] = length[curr.x] + edge.cost;
                open.push(next);
            }
        }
    }

    return total;
}

// removes all edges that have timestamp strictly later than 'point' from the graph
void STPEdgeGraph::removeAfter(uint32_t point) {
    if (addedEdges.empty()) return;
    for (ptrdiff_t i = addedEdges.size()-1; i >= 0; --i) {
        EdgeRef eRef = addedEdges[i];
        auto &edge = store.getEdge(eRef);
        if (edge.setTime <= point) return;  // edges appear in 'addedEdges' in timestamp order
        // edges are added in the same order to all three lists - no need to check the values of incoming / outgoing
        incoming[edge.to.x].pop_back();
        outgoing[edge.from.x].pop_back();
        addedEdges.pop_back();
        edge.setTime = 0;
    }
}


