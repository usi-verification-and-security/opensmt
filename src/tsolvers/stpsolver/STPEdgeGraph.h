#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"
#include "STPMapper.h"

// helper struct to return results of DFS
struct DFSResult {
    vec<bool> visited;              // map of which vertices were visited
    vec<ptrdiff_t> distance;  // map of distances to each visited vertex
    size_t total;                           // sum of all edges each vertex appears in
};

struct EdgeGraph {
    vec<EdgeRef> addedEdges;
    vec<EdgeRef> deductions;
    vec<vec<EdgeRef>> incoming, outgoing;

    void addEdge(EdgeRef e, VertexRef from, VertexRef to);
    void clear();
};

// stores edges set as true and finds consequences of each added edge
class STPGraphManager {

    STPStore & store;

    STPMapper & mapper;

    EdgeGraph graph;

    uint32_t timestamp;        // timestamp of the latest 'setTrue' call

    DFSResult dfsSearch(VertexRef init, bool forward);

    void setDeduction(EdgeRef e);

public:
    explicit STPGraphManager(STPStore &store, STPMapper &mapper) : store(store), mapper(mapper), timestamp(0) {}
    bool isTrue(EdgeRef e) const;
    uint32_t getAddedCount() const { return timestamp; }
    void setTrue(EdgeRef e, PtAsgn asgn);
    vec<EdgeRef> findConsequences(EdgeRef e);
    void findExplanation(EdgeRef e, vec<PtAsgn> &v);
    void removeAfter(uint32_t point);
    void clear();
};


#endif //OPENSMT_STPEDGEGRAPH_H
