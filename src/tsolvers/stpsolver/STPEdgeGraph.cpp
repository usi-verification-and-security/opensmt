#ifndef OPENSMT_STPEDGEGRAPH_C
#define OPENSMT_STPEDGEGRAPH_C

#include <stack>
#include "STPEdgeGraph.h"

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

template<class T> bool STPGraphManager<T>::isTrue(EdgeRef e) const {
    return e != EdgeRef_Undef && store.getEdge(e).setTime != 0;
}

template<class T> void STPGraphManager<T>::setTrue(EdgeRef e, PtAsgn asgn) {
    Edge<T> &edge = store.getEdge(e);
    if (edge.setTime != 0) return;              // edge was already set to true - it is already stored

    ++timestamp;
    edge.setTime = timestamp;
    mapper.setAssignment(e, asgn);
    graph.addEdge(e, edge.from, edge.to);
}

template<class T> void STPGraphManager<T>::setDeduction(EdgeRef e) {
    deductions.push_back(e);
    store.getEdge(e).setTime = timestamp;
}

// Searches through the graph to find consequences of currently assigned edges, starting from 'e'
template<class T> std::vector<EdgeRef> STPGraphManager<T>::findConsequences(EdgeRef e) {
    size_t n = store.vertexNum();

    auto &start = store.getEdge(e);
    // find potential starts/ends of an edge with a path going through 'e'
    auto aRes = dfsSearch(start.from, false);
    auto bRes = dfsSearch(start.to, true);

    // we scan through the side which appears in fewer total edges
    auto &thisRes = aRes.total < bRes.total ? aRes : bRes;
    auto &otherRes = aRes.total < bRes.total ? bRes : aRes;

    std::vector<EdgeRef> ret;
    // for each (WLOG) 'a', go through its edges and find each 'a -> b' edge that has cost higher than length found by DFS
    // such edges are consequences of the current graph
    for (uint32_t i = 0; i < n; ++i) {
        if (!thisRes.visited[i]) continue;
        for (auto eRef : mapper.edgesOf(VertexRef{i})) {
            if (eRef == e) continue;
            const Edge<T> &edge = store.getEdge(eRef);
            auto thisSide = (aRes.total < bRes.total) ? edge.from.x : edge.to.x;
            auto otherSide = (aRes.total < bRes.total) ? edge.to.x : edge.from.x;
            if (thisSide == i && otherRes.visited[otherSide]
                && edge.cost >= thisRes.distance[thisSide] + start.cost + otherRes.distance[otherSide]) {
                if (edge.setTime == 0) {
                    ret.push_back(eRef);
                    setDeduction(eRef);
                }
            }
        }
    }

    return ret;
}

// DFS through the graph to find shortest paths to all reachable vertices from 'init' in the given direction
template<class T> typename STPGraphManager<T>::DFSResult STPGraphManager<T>::dfsSearch(VertexRef init, bool forward) {
    std::vector<bool> visited(store.vertexNum());
    std::vector<SafeInt> length(store.vertexNum());
    size_t total = 0;
    std::stack<VertexRef> open;
    visited[init.x] = true;
    length[init.x] = 0;
    open.push(init);

    while (!open.empty()) {
        VertexRef curr = open.top(); open.pop();
        auto &toScan = forward ? graph.outgoing[curr.x] : graph.incoming[curr.x];
        for (auto eRef : toScan) {
            const Edge<T> &edge = store.getEdge(eRef);
            auto next = forward ? edge.to : edge.from;
            if (!visited[next.x]) {
                visited[next.x] = true;
                open.push(next);
                length[next.x] = length[curr.x] + edge.cost;
                total += mapper.edgesOf(next).size();
            } else if (length[next.x] > length[curr.x] + edge.cost) {
                length[next.x] = length[curr.x] + edge.cost;
                open.push(next);
            }
        }
    }

    return DFSResult{std::move(visited), std::move(length), total};
}

// removes all edges that have timestamp strictly later than 'point' from the graph
template<class T> void STPGraphManager<T>::removeAfter(uint32_t point) {
    if (graph.addedEdges.empty()) return;

    for (int i = graph.addedEdges.size()-1; i >= 0; --i) {
        EdgeRef eRef = graph.addedEdges[i];
        auto &edge = store.getEdge(eRef);
        if (edge.setTime <= point) {  // edges appear in 'addedEdges' in timestamp order
            timestamp = edge.setTime;
            break;
        }
        // edges are added in the same order to all three lists - no need to check the values of incoming / outgoing
        graph.incoming[edge.to.x].pop_back();
        graph.outgoing[edge.from.x].pop_back();
        graph.addedEdges.pop_back();
        edge.setTime = 0;
        mapper.removeAssignment(eRef);
    }

    if (deductions.empty()) return;
    for (int i = deductions.size() - 1; i >= 0; --i) {
        EdgeRef ded = deductions[i];
        auto &edge = store.getEdge(ded);
        if (edge.setTime <= point) {
            return;
        }

        edge.setTime = 0;
        deductions.pop_back();
    }
}

template<class T> void STPGraphManager<T>::findExplanation(EdgeRef e, vec<PtAsgn> &v) {
    const Edge<T> &expl = store.getEdge(e);
    if (mapper.getAssignment(e) != PtAsgn_Undef) {      // explanation for explicitly assigned edge is trivial
        v.push(mapper.getAssignment(e));
        return;
    }

    std::vector<EdgeRef> visited(store.vertexNum(), EdgeRef_Undef);
    std::vector<SafeInt> length(store.vertexNum());
    std::stack<VertexRef> open;

    open.push(expl.from);
    while (!open.empty()) {
        auto curr = open.top(); open.pop();
        if (curr == expl.to && length[curr.x] <= expl.cost) break;
        for (auto eRef : graph.outgoing[curr.x]) {
            if (eRef == e) continue;
            const Edge<T> &edge = store.getEdge(eRef);
            if (edge.setTime > expl.setTime) continue;
            assert(mapper.getAssignment(eRef) != PtAsgn_Undef); // deductions aren't stored in graph

            auto next = edge.to;
            if (visited[next.x] == EdgeRef_Undef || length[next.x] > length[curr.x] + edge.cost) {
                visited[next.x] = eRef;
                length[next.x] = length[curr.x] + edge.cost;
                open.push(next);
            }
        }
    }

    auto backtrack = visited[expl.to.x];
    while (true) {
        assert( backtrack != EdgeRef_Undef);
        const Edge<T> &edge = store.getEdge(backtrack);
        assert( mapper.getAssignment(backtrack) != PtAsgn_Undef );
        v.push(mapper.getAssignment(backtrack));
        if (edge.from == expl.from) break;
        backtrack = visited[edge.from.x];
    }
}

template<class T> void STPGraphManager<T>::clear() {
    timestamp = 0;
    graph.clear();
}

#endif //OPENSMT_STPEDGEGRAPH_C