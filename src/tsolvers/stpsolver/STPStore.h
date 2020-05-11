#ifndef OPENSMT_STPSTORE_H
#define OPENSMT_STPSTORE_H

#include <cstdint>
#include <vector>
#include <Number.h>
#include <SolverTypes.h>

struct VertexRef {
    uint32_t x;
    inline bool operator==(VertexRef other) const { return x == other.x; }
    explicit operator bool() const { return x != INT32_MAX; }
};

struct EdgeRef {
    uint32_t x;
    inline bool operator==(EdgeRef other) const { return x == other.x; }
    explicit operator bool() const { return x != INT32_MAX; }
};

static VertexRef VertRef_Undef = VertexRef { INT32_MAX };
static EdgeRef EdgeRef_Undef = EdgeRef { INT32_MAX };

struct Edge {
    VertexRef from, to;
    EdgeRef neg;
    opensmt::Number cost;
};

class STPStore {
private:
    std::vector<VertexRef> verts;           // list of all created vertices
    std::vector<Edge> edges;                //                     edges
    std::vector<std::vector<EdgeRef>> edgesOfVertex;
public:
    VertexRef createVertex();
    EdgeRef createEdge(VertexRef from, VertexRef to, opensmt::Number cost);
    void setTrue(EdgeRef e);

    size_t vertexNum() const  { return verts.size(); }
    size_t edgeNum() const { return edges.size(); }
    Edge & getEdge(EdgeRef e) { return edges[e.x]; }
    const std::vector<EdgeRef> & getEdgesOf(VertexRef v) const { return edgesOfVertex[v.x]; }
    void setNegation(EdgeRef a, EdgeRef b);
    EdgeRef hasNeighbour(VertexRef from, VertexRef to);
};

#endif //OPENSMT_STPSTORE_H
