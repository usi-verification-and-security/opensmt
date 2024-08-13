#ifndef OPENSMT_STPVALMAPPER_HPP
#define OPENSMT_STPVALMAPPER_HPP

#include "STPGraphManager.h"

#include <unordered_map>
// implementations of template functions #included below class definition

namespace opensmt {
// holds the mapping from vertices to their values
template<class T>
class STPModel {
public:
    STPModel(STPStore<T> & store, EdgeGraph graph) : store(store), graph(std::move(graph)) {}

    void createModel();

    bool hasValue(VertexRef v) const { return valMap.count(v.x); }

    T getValue(VertexRef v) const {
        return Converter<T>::getValue(0) - valMap.at(v.x);
    } // valid assignment is actually the inverse of distance

    std::unordered_map<VertexRef, T, VertexRefHash> getAllValues() const;

    EdgeGraph const & getGraph() const { return graph; }

private:
    std::vector<VertexRef> vertsInGraph() const;

    VertexRef addStartingPoint();

    void bellmanFord(VertexRef start);

    void shiftZero();

    STPStore<T> & store;
    EdgeGraph graph;
    std::unordered_map<uint32_t, T> valMap; // for each vertex, distance from the added starting vertex
};
} // namespace opensmt

#include "STPModel_implementations.hpp"

#endif // OPENSMT_STPVALMAPPER_HPP
