#ifndef OPENSMT_STPEDGEGRAPH_H
#define OPENSMT_STPEDGEGRAPH_H

#include "STPStore.h"

namespace opensmt {
struct EdgeGraph {
    std::vector<EdgeRef> addedEdges;
    std::vector<std::vector<EdgeRef>> incoming, outgoing;

    void addEdge(EdgeRef e, VertexRef from, VertexRef to);

    void clear();

    bool isEmpty() const;
};
} // namespace opensmt

#endif // OPENSMT_STPEDGEGRAPH_H
