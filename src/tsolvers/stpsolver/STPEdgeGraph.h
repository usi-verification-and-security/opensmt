#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"
#include "STPMapper.h"
// implementations of template functions #included below class definitions

struct EdgeGraph {
    std::vector<EdgeRef> addedEdges;
    std::vector<std::vector<EdgeRef>> incoming, outgoing;

    void addEdge(EdgeRef e, VertexRef from, VertexRef to);

    void clear();
};

// stores edges set as true and finds consequences of each added edge
template<class T>
class STPGraphManager {
private:
    // helper struct to return results of DFS
    struct DFSResult {
        std::vector<bool> visited;      // map of which vertices were visited
        std::vector<T> distance;        // map of distances to each visited vertex
        size_t total{};                 // sum of all edges each vertex appears in

        DFSResult(std::vector<bool> &&vis, std::vector<T> &&dist, size_t total) :
                visited(std::move(vis)), distance(std::move(dist)), total(total) {}
    };

    STPStore<T> &store;

    STPMapper<T> &mapper;

    EdgeGraph graph;

    uint32_t timestamp;        // timestamp of the latest 'setTrue' call

    std::vector<EdgeRef> deductions;

    DFSResult dfsSearch(VertexRef init, bool forward);

    void setDeduction(EdgeRef e);

public:
    explicit STPGraphManager(STPStore<T> &store, STPMapper<T> &mapper) : store(store), mapper(mapper), timestamp(0) {}

    const EdgeGraph &getGraph() const { return graph; }

    bool isTrue(EdgeRef e) const;

    uint32_t getAddedCount() const { return timestamp; }

    void setTrue(EdgeRef e, PtAsgn asgn);

    std::vector<EdgeRef> findConsequences(EdgeRef e);

    void findExplanation(EdgeRef e, vec<PtAsgn> &v);

    void removeAfter(uint32_t point);

    void clear();
};

#include "STPEdgeGraph.cpp"

#endif //OPENSMT_STPEDGEGRAPH_H
