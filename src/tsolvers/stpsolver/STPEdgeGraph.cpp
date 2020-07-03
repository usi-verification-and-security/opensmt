#include <stack>
#include "STPEdgeGraph.h"

EdgeGraph::EdgeGraph(const EdgeGraph &other) {
    other.addedEdges.copyTo(addedEdges);
    other.incoming.copyTo(incoming);
    other.outgoing.copyTo(outgoing);
    other.deductions.copyTo(deductions);
}

void EdgeGraph::addEdge(EdgeRef e, VertexRef from, VertexRef to) {
    auto max = std::max(from.x, to.x);
    if (incoming.size() <= max) {
        incoming.growTo(max + 1);
        outgoing.growTo(max + 1);
    }
    addedEdges.push(e);
    incoming[to.x].push(e);
    outgoing[from.x].push(e);
}

void EdgeGraph::clear() {
    addedEdges.clear();
    incoming.clear();
    outgoing.clear();
}

bool STPGraphManager::isTrue(EdgeRef e) const {
    return e != EdgeRef_Undef && store.getEdge(e).setTime != 0;
}

void STPGraphManager::setTrue(EdgeRef e, PtAsgn asgn) {
    Edge &edge = store.getEdge(e);
    if (edge.setTime != 0) return;              // edge was already set to true - it is already stored

    ++timestamp;
    edge.setTime = timestamp;
    mapper.setAssignment(e, asgn);
    graph.addEdge(e, edge.from, edge.to);
}

void STPGraphManager::setDeduction(EdgeRef e) {
    graph.deductions.push(e);
    store.getEdge(e).setTime = timestamp;
}

// Searches through the graph to find consequences of currently assigned edges, starting from 'e'
vec<EdgeRef> STPGraphManager::findConsequences(EdgeRef e) {
    size_t n = store.vertexNum();

    auto start = store.getEdge(e);
    // find potential starts/ends of an edge with a path going through 'e'
    auto aRes = dfsSearch(start.from, false);
    auto bRes = dfsSearch(start.to, true);

    // we scan through the side which appears in fewer total edges
    auto &thisRes = aRes.total < bRes.total ? aRes : bRes;
    auto &otherRes = aRes.total < bRes.total ? bRes : aRes;

    vec<EdgeRef> ret;
    // for each (WLOG) 'a', go through its edges and find each 'a -> b' edge that has cost higher than length found by DFS
    // such edges are consequences of the current graph
    for (uint32_t i = 0; i < n; ++i) {
        if (!thisRes.visited[i]) continue;
        for (auto eRef : mapper.edgesOf(VertexRef{i})) {
            if (eRef == e) continue;
            Edge &edge = store.getEdge(eRef);
            auto thisSide = (aRes.total < bRes.total) ? edge.from.x : edge.to.x;
            auto otherSide = (aRes.total < bRes.total) ? edge.to.x : edge.from.x;
            if (thisSide == i && otherRes.visited[otherSide]
                && edge.cost >= thisRes.distance[thisSide] + start.cost + otherRes.distance[otherSide]) {
                if (edge.setTime == 0) {
                    ret.push(eRef);
                    setDeduction(eRef);
                }
            }
        }
    }

    return ret;
}

// DFS through the graph to find shortest paths to all reachable vertices from 'init' in the given direction
DFSResult STPGraphManager::dfsSearch(VertexRef init, bool forward) {
    vec<bool> visited(store.vertexNum());
    vec<ptrdiff_t> length(store.vertexNum());
    size_t total = 0;
    std::stack<VertexRef> open;
    visited[init.x] = true;
    length[init.x] = 0;
    open.push(init);

    while (!open.empty()) {
        VertexRef curr = open.top(); open.pop();
        auto &toScan = forward ? graph.outgoing[curr.x] : graph.incoming[curr.x];
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

    return DFSResult{std::move(visited), std::move(length), total};
}

// removes all edges that have timestamp strictly later than 'point' from the graph
void STPGraphManager::removeAfter(uint32_t point) {
    if (!graph.addedEdges.size()) return;

    for (int i = graph.addedEdges.size()-1; i >= 0; --i) {
        EdgeRef eRef = graph.addedEdges[i];
        auto &edge = store.getEdge(eRef);
        if (edge.setTime <= point) {  // edges appear in 'addedEdges' in timestamp order
            timestamp = edge.setTime;
            break;
        }
        // edges are added in the same order to all three lists - no need to check the values of incoming / outgoing
        graph.incoming[edge.to.x].pop();
        graph.outgoing[edge.from.x].pop();
        graph.addedEdges.pop();
        edge.setTime = 0;
        mapper.removeAssignment(eRef);
    }

    if (!graph.deductions.size()) return;
    for (int i = graph.deductions.size() - 1; i >= 0; --i) {
        EdgeRef ded = graph.deductions[i];
        auto &edge = store.getEdge(ded);
        if (edge.setTime <= point) {
            return;
        }

        edge.setTime = 0;
        graph.deductions.pop();
    }
}

void STPGraphManager::findExplanation(EdgeRef e, vec<PtAsgn> &v) {
    Edge &expl = store.getEdge(e);
    if (mapper.getAssignment(e) != PtAsgn_Undef) {
        v.push(mapper.getAssignment(e));
        return;
    }

    vec<EdgeRef> visited(store.vertexNum(), EdgeRef_Undef);
    vec<ptrdiff_t> length(store.vertexNum());
    std::stack<VertexRef> open;

    open.push(expl.from);
    while (!open.empty()) {
        auto curr = open.top(); open.pop();
        if (curr == expl.to && length[curr.x] <= expl.cost) break;
        for (auto eRef : graph.outgoing[curr.x]) {
            if (eRef == e) continue;
            Edge &edge = store.getEdge(eRef);
            if (edge.setTime > expl.setTime) continue;
            if (mapper.getAssignment(eRef) == PtAsgn_Undef) continue;

            auto next = edge.to;
            if (visited[next.x] == EdgeRef_Undef || length[next.x] > length[curr.x] + edge.cost) {
                visited[next.x] = eRef;
                length[next.x] = length[curr.x] + edge.cost;
                open.push(next);
            }
        }
    }

    auto backtrack = visited[expl.to.x];
    assert( backtrack != EdgeRef_Undef);
    while (true) {
        Edge &edge = store.getEdge(backtrack);
        assert( mapper.getAssignment(backtrack) != PtAsgn_Undef );
        v.push(mapper.getAssignment(backtrack));
        if (edge.from == expl.from) break;
        backtrack = visited[edge.from.x];
    }
}

void STPGraphManager::clear() {
    timestamp = 0;
    graph.clear();
}



