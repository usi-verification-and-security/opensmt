#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"
#include "STPMapper.h"

class STPEdgeGraph {

    STPStore & store;

    STPMapper & mapper;

    std::vector<EdgeRef> addedEdges;

    using AdjList = std::vector<EdgeRef>;
    std::vector<AdjList> incoming, outgoing;

public:
    explicit STPEdgeGraph(STPStore &store, STPMapper &mapper) : store(store), mapper(mapper) {}
    bool isTrue(EdgeRef e);
    void setTrue(EdgeRef e);
    void findConsequences(EdgeRef e);
};


#endif //OPENSMT_STPEDGEGRAPH_H
