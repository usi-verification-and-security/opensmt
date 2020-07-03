#ifndef OPENSMT_STPVALMAPPER_HPP
#define OPENSMT_STPVALMAPPER_HPP

#include "STPEdgeGraph.h"

class STPModel {
private:
    STPStore &store;
    EdgeGraph graph;
    std::unordered_map<uint32_t, ptrdiff_t> valMap;

    vec<VertexRef> vertsInGraph() const;
    VertexRef addStartingPoint();
    void bellmanFord(VertexRef start);
    void shiftZero();
public:
    STPModel(STPStore &store, EdgeGraph &&graph) : store(store), graph(std::move(graph)) {}
    void createModel();
    bool hasValue(VertexRef v) const { return valMap.count(v.x); }
    ptrdiff_t getValue(VertexRef v) const { return -valMap.at(v.x); }
};


#endif //OPENSMT_STPVALMAPPER_HPP
