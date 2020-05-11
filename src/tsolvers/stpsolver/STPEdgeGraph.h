#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"

class STPEdgeGraph {

    STPStore & store;

    using AdjList = std::vector<EdgeRef>;
    std::vector<AdjList> incoming, outgoing;

public:
    explicit STPEdgeGraph(STPStore & store) : store(store) {}
    bool isTrue(EdgeRef e);
    void setTrue(EdgeRef e);
    void getConsequences(EdgeRef e);
};


#endif //OPENSMT_STPEDGEGRAPH_H
