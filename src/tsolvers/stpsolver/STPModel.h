#ifndef OPENSMT_STPVALMAPPER_HPP
#define OPENSMT_STPVALMAPPER_HPP

#include "STPEdgeGraph.h"

// holds the mapping from vertices to their values
template<class T> class STPModel {
private:
    STPStore<T> &store;
    EdgeGraph graph;
    std::unordered_map<uint32_t, T> valMap;  // for each vertex, distance from the added starting vertex

    vec<VertexRef> vertsInGraph() const;
    VertexRef addStartingPoint();
    void bellmanFord(VertexRef start);
    void shiftZero();
public:
    STPModel(STPStore<T> &store, const EdgeGraph& graph) : store(store), graph(graph) {}
    void createModel();
    bool hasValue(VertexRef v) const { return valMap.count(v.x); }
    T getValue(VertexRef v) const { return -valMap.at(v.x); } // valid assignment is actually the inverse of distance
};


#include "STPModel.cpp" // FIXME
#endif //OPENSMT_STPVALMAPPER_HPP
