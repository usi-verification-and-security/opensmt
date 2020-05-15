#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"
#include "STPMapper.h"

class STPEdgeGraph {

    STPStore & store;

    STPMapper & mapper;

    uint32_t addedCount;

    std::vector<std::pair<EdgeRef, uint32_t>> addedEdges;    // FIXME: Probably should be stored somewhere else
                                                             // FIXME: can contain duplicates

    using AdjList = std::vector<EdgeRef>;
    std::vector<AdjList> incoming, outgoing;

public:
    explicit STPEdgeGraph(STPStore &store, STPMapper &mapper) : store(store), mapper(mapper), addedCount(0) {}
    bool isTrue(EdgeRef e) const;
    void setTrue(EdgeRef e);
    void findConsequences(EdgeRef e);
};


#endif //OPENSMT_STPEDGEGRAPH_H
