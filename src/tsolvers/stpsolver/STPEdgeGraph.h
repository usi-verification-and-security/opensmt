#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"
#include "STPMapper.h"

struct EdgeGraph {
    vec<EdgeRef> addedEdges;
    vec<vec<EdgeRef>> incoming, outgoing;

    EdgeGraph() = default;
    EdgeGraph(const EdgeGraph &other);
    void addEdge(EdgeRef e, VertexRef from, VertexRef to);
    void clear();
};

// stores edges set as true and finds consequences of each added edge
template<class T> class STPGraphManager {
private:
    // helper struct to return results of DFS
    struct DFSResult {
        vec<bool> visited;              // map of which vertices were visited
        vec<T> distance;        // map of distances to each visited vertex
        size_t total;                   // sum of all edges each vertex appears in
    };

    STPStore<T> & store;

    STPMapper<T> & mapper;

    EdgeGraph graph;

    uint32_t timestamp;        // timestamp of the latest 'setTrue' call

    vec<EdgeRef> deductions;

    DFSResult dfsSearch(VertexRef init, bool forward);

    void setDeduction(EdgeRef e);

public:
    explicit STPGraphManager(STPStore<T> &store, STPMapper<T> &mapper) : store(store), mapper(mapper), timestamp(0) {}
    const EdgeGraph & getGraph() const { return graph; }
    bool isTrue(EdgeRef e) const;
    uint32_t getAddedCount() const { return timestamp; }
    void setTrue(EdgeRef e, PtAsgn asgn);
    vec<EdgeRef> findConsequences(EdgeRef e);
    void findExplanation(EdgeRef e, vec<PtAsgn> &v);
    void removeAfter(uint32_t point);
    void clear();
};

#include "STPEdgeGraph.cpp" // FIXME
#endif //OPENSMT_STPEDGEGRAPH_H
