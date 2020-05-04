#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"

class STPEdgeGraph {
    STPStore & store;
    std::vector<bool> assigned;

public:
    STPEdgeGraph(STPStore & store) : store(store) {}
    bool isTrue(EdgeRef e);
    void setTrue(EdgeRef e);
};


#endif //OPENSMT_STPEDGEGRAPH_H
