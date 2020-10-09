#ifndef OPENSMT_STPVALMAPPER_HPP
#define OPENSMT_STPVALMAPPER_HPP

#include "STPEdgeGraph.h"
// implementations of template functions #included below class definition

// holds the mapping from vertices to their values
// FIXME: Incomplete for now. Will be fixed with new model interface
template<class T>
class STPModel {
private:
    STPStore<T> &store;
    EdgeGraph graph;
    std::unordered_map<uint32_t, T> valMap;  // for each vertex, distance from the added starting vertex

    std::vector<VertexRef> vertsInGraph() const;

    VertexRef addStartingPoint();

    void bellmanFord(VertexRef start);

    void shiftZero();

public:
    STPModel(STPStore<T> &store, EdgeGraph graph) : store(store), graph(std::move(graph)) {}

    void createModel();

    bool hasValue(VertexRef v) const { return valMap.count(v.x); }

    T getValue(VertexRef v) const { return -valMap.at(v.x); } // valid assignment is actually the inverse of distance
};

#include "STPModel.cpp"

#endif //OPENSMT_STPVALMAPPER_HPP
