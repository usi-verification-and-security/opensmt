#include <stack>
#include "STPEdgeGraph.h"

bool STPEdgeGraph::isTrue(EdgeRef e) const {
    for (auto &&pair : addedEdges) {
        if (pair.first == e) return true;
    }
    return false;
}

void STPEdgeGraph::setTrue(EdgeRef e) {
    addedEdges.emplace_back(e, ++addedCount);
    const Edge &edge = store.getEdge(e);
    auto max = std::max(edge.from.x, edge.to.x);
    if (incoming.size() <= max) {
        incoming.resize(max + 1);
        outgoing.resize(max + 1);
    }

    outgoing[edge.from.x].push_back(e);
    incoming[edge.to.x].push_back(e);
}

void STPEdgeGraph::findConsequences(EdgeRef e) {
    size_t n = store.vertexNum();
    size_t aTotal = 0, bTotal = 0;

    std::vector<bool> visitedA(n), visitedB(n);             // TODO: Replace with maps?
    std::vector<opensmt::Number> lengthA(n), lengthB(n);

    std::stack<VertexRef> open;
    auto start = store.getEdge(e);

    visitedA[start.from.x] = true;
    lengthA[start.from.x] = 0;
    open.push(start.from);
    // TODO: similar code twice. Refactor?
    while (!open.empty()) {
        VertexRef curr = open.top(); open.pop();
        for (auto eRef : incoming[curr.x]) {
            const Edge &edge = store.getEdge(eRef);
            if (!visitedA[edge.from.x]) {
                visitedA[edge.from.x] = true;
                lengthA[edge.from.x] = lengthA[curr.x] + edge.cost;
                aTotal += mapper.edgesOf(edge.from).size();
                open.push(edge.from);
            } else if (lengthA[edge.from.x] > lengthA[curr.x] + edge.cost) {
                lengthA[edge.from.x] = lengthA[curr.x] + edge.cost;
                open.push(edge.from);
            }
        }
    }

    visitedB[start.to.x] = true;
    lengthB[start.to.x] = 0;
    open.push(start.to);
    while (!open.empty()) {
        VertexRef curr = open.top(); open.pop();
        for (auto eRef : outgoing[curr.x]) {
            const Edge &edge = store.getEdge(eRef);
            if (!visitedB[edge.to.x]) {
                visitedB[edge.to.x] = true;
                lengthB[edge.to.x] = lengthB[curr.x] + edge.cost;
                bTotal += mapper.edgesOf(edge.to).size();
                open.push(edge.to);
            } else if (lengthB[edge.from.x] > lengthB[curr.x] + edge.cost) {
                lengthB[edge.to.x] = lengthB[curr.x] + edge.cost;
                open.push(edge.to);
            }
        }
    }

    if (aTotal <= bTotal) {
        for (uint32_t i = 0; i < n; ++i) {
            if (!visitedA[i]) continue;
            for (auto eRef : mapper.edgesOf(VertexRef{i})) {
                if (eRef == e) continue;
                const Edge & edge = store.getEdge(eRef);
                if (edge.from.x == i && visitedB[edge.to.x] && edge.cost >= lengthA[i] + start.cost + lengthB[edge.to.x]) {
                    addedEdges.emplace_back(eRef, addedCount);
                    incoming[edge.to.x].push_back(eRef);
                    outgoing[edge.from.x].push_back(eRef);
                }
            }
        }
    } else {
        for (uint32_t i = 0; i < n; ++i) {
            if (!visitedB[i]) continue;
            for (auto eRef : mapper.edgesOf(VertexRef{i})) {
                if (eRef == e) continue;
                const Edge & edge = store.getEdge(eRef);
                if (edge.to.x == i && visitedA[edge.from.x] && edge.cost >= lengthA[edge.from.x] + start.cost + lengthB[i]) {
                    addedEdges.emplace_back(eRef, addedCount);
                    incoming[edge.to.x].push_back(eRef);
                    outgoing[edge.from.x].push_back(eRef);
                }
            }
        }
    }
}

void STPEdgeGraph::removeAfter(uint32_t point) {
    if (addedEdges.empty()) return;
    for (ptrdiff_t i = addedEdges.size()-1; i >= 0; --i) {
        auto &pair = addedEdges[i];
        if (pair.second <= point) return;
        auto &edge = store.getEdge(pair.first);
        // edges are added in the same order to all three - no need to check the values of incoming / outgoing
        incoming[edge.to.x].pop_back();
        outgoing[edge.from.x].pop_back();
        addedEdges.pop_back();
    }
}


