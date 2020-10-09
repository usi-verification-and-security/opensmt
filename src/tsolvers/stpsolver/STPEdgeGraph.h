#ifndef OPENSMT_STPEDGEGRAPH_HPP
#define OPENSMT_STPEDGEGRAPH_HPP

#include "STPStore.h"

struct EdgeGraph {
    std::vector<EdgeRef> addedEdges;
    std::vector<std::vector<EdgeRef>> incoming, outgoing;

    void addEdge(EdgeRef e, VertexRef from, VertexRef to);

    void clear();
};

#endif //OPENSMT_STPEDGEGRAPH_HPP
