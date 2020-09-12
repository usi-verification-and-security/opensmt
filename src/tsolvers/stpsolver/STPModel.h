#ifndef OPENSMT_STPVALMAPPER_HPP
#define OPENSMT_STPVALMAPPER_HPP

#include "STPEdgeGraph.h"

// holds the mapping from vertices to their values
class STPModel {
private:
    STPStore &store;
    EdgeGraph graph;
    std::unordered_map<uint32_t, SafeInt> valMap;  // for each vertex, distance from the added starting vertex

    vec<VertexRef> vertsInGraph() const;
    VertexRef addStartingPoint();
    void bellmanFord(VertexRef start);
    void shiftZero();
public:
    STPModel(STPStore &store, const EdgeGraph& graph) : store(store), graph(graph) {}
    void createModel();
    bool hasValue(VertexRef v) const { return valMap.count(v.x); }
    SafeInt getValue(VertexRef v) const { return -valMap.at(v.x); } // valid assignment is actually the inverse of distance
};


#endif //OPENSMT_STPVALMAPPER_HPP
