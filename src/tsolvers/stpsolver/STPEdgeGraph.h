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

// stores edges set as true and finds consequences of each added edge
class STPEdgeGraph {

    STPStore & store;

    STPMapper & mapper;

    uint32_t addedCount;                // timestamp of the latest 'setTrue' call

    vec<EdgeRef> addedEdges;    // list of all edges set as true and their consequences

    using AdjList = vec<EdgeRef>;
    vec<AdjList> incoming, outgoing; // for each vertex, a list of set edges coming to/from that vertex

    DFSResult dfsSearch(VertexRef init, bool forward);

public:
    explicit STPEdgeGraph(STPStore &store, STPMapper &mapper) : store(store), mapper(mapper), addedCount(0) {}
    bool isTrue(EdgeRef e) const;
    uint32_t getAddedCount() const { return addedCount; }
    void setTrue(EdgeRef e, PtAsgn asgn);
    void findConsequences(EdgeRef e);
    void findExplanation(EdgeRef e, vec<PtAsgn> &v);
    void removeAfter(uint32_t point);
    void clear();
};


#endif //OPENSMT_STPEDGEGRAPH_H
