#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include <memory>
#include "STPStore.h"
#include "STPMapper.h"

// helper struct to return results of DFS
struct DFSResult {
    std::unique_ptr<std::vector<bool>> visited;              // map of which vertices were visited
    std::unique_ptr<std::vector<opensmt::Number>> distance;  // map of distances to each visited vertex
    size_t total;                                            // sum of all edges each vertex appears in
};

// stores edges set as true and finds consequences of each added edge
class STPEdgeGraph {

    STPStore & store;

    STPMapper & mapper;

    uint32_t addedCount;                // timestamp of the latest 'setTrue' call

    std::vector<EdgeRef> addedEdges;    // list of all edges set as true and their consequences

    using AdjList = std::vector<EdgeRef>;
    std::vector<AdjList> incoming, outgoing; // for each vertex, a list of 'true' edges coming to/from that vertex

    DFSResult dfsSearch(VertexRef init, bool forward);

public:
    explicit STPEdgeGraph(STPStore &store, STPMapper &mapper) : store(store), mapper(mapper), addedCount(0) {}
    bool isTrue(EdgeRef e) const;
    uint32_t getAddedCount() const { return addedCount; }
    void setTrue(EdgeRef e, PtAsgn asgn);
    void findConsequences(EdgeRef e);
    void findExplanation(EdgeRef e, vec<PtAsgn> &v);
    void removeAfter(uint32_t point);
};


#endif //OPENSMT_STPEDGEGRAPH_H
