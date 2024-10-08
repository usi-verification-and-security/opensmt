#ifndef OPENSMT_STPGRAPHMANAGER_H
#define OPENSMT_STPGRAPHMANAGER_H

#include "STPEdgeGraph.h"
#include "STPMapper.h"
#include "STPStore.h"
// implementations of template functions #included below class definitions

namespace opensmt {
// stores edges set as true and finds consequences of each added edge
template<class T>
class STPGraphManager {
public:
    explicit STPGraphManager(STPStore<T> & store, STPMapper<T> & mapper) : store(store), mapper(mapper), timestamp(0) {}

    EdgeGraph const & getGraph() const { return graph; }

    bool isTrue(EdgeRef e) const;

    uint32_t getAddedCount() const { return timestamp; }

    void setTrue(EdgeRef e, PtAsgn asgn);

    std::vector<EdgeRef> findConsequences(EdgeRef e);

    void findExplanation(EdgeRef e, vec<PtAsgn> & v);

    void removeAfter(uint32_t point);

    void clear();

private:
    // helper struct to return results of DFS
    struct DFSResult {
        std::vector<bool> visited; // map of which vertices were visited
        std::vector<T> distance;   // map of distances to each visited vertex
        size_t total{};            // sum of all edges each vertex appears in

        DFSResult(std::vector<bool> && vis, std::vector<T> && dist, size_t total)
            : visited(std::move(vis)),
              distance(std::move(dist)),
              total(total) {}
    };

    DFSResult dfsSearch(VertexRef init, bool forward);

    void setDeduction(EdgeRef e);

    STPStore<T> & store;

    STPMapper<T> & mapper;

    EdgeGraph graph;

    uint32_t timestamp; // timestamp of the latest 'setTrue' call

    std::vector<EdgeRef> deductions;
};
} // namespace opensmt

#include "STPGraphManager_implementations.hpp"

#endif // OPENSMT_STPGRAPHMANAGER_H
